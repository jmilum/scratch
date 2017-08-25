(ns user
  (:require
   [clojure.main]
   [clojure.java.io :as jio]
   ;[clojure.core.reducers :as r]
   [clojure.pprint :refer [pprint pp]]
   [clojure.repl :refer [apropos dir doc find-doc pst source]]
   [clojure.set :as set]
   [clojure.data.csv :as csv]
   [cognitect.transit :as t]
   [clojure.string :as str]
   [clojure.math.numeric-tower :as math]
   [clojure.tools.namespace.repl :refer [refresh refresh-all]]
   [clojure.algo.generic.functor :as f]
   [criterium.core :refer [bench quick-bench]]
   [clojure.core.matrix :as m]
   [clojure.core.matrix.linear :as ml]
   [clojure.core.matrix.operators :as mo]
   [com.hypirion.clj-xchart :as chart]
   [complex.core :as c]
   [cquad.core :as cquad])
   ;[infix.core :refer [base-env]]
   ;[infix.math :refer [defbinary]]
   ;[infix.macros :refer [infix from-string]]
   ;[mikera.cljutils.loops :as loops])
  (:import
   (java.io File FileNotFoundException Reader BufferedReader)
   (java.util Date UUID)
   (clojure.lang BigInt Ratio)
   (org.apache.commons.math3.complex Complex)))


(set! *warn-on-reflection* true)
(set! *unchecked-math* true)

(defmacro defmethod*
  "closure over defmethod to bind the dispatch-val with :as"
  [multifn dispatch-val & fn-tail]
  (let [[kw n & body] fn-tail]
    (if (= :as kw)
      `(let [~n ~dispatch-val]
         (defmethod ~multifn ~dispatch-val ~body))
      `(defmethod ~dispatch-val ~fn-tail))))

(defmacro when-let*
  "allow multiple bindings in when-let"
  ([bindings & body]
   (if (seq bindings)
     `(when-let [~(first bindings) ~(second bindings)]
        (when-let* ~(drop 2 bindings) ~@body))
     `(do ~@body))))

(defmacro if-let*
  "allow multiple bindings in if-let"
  ([bindings then]
   `(if-let* ~bindings ~then nil))
  ([bindings then else]
   (if (seq bindings)
     `(if-let [~(first bindings) ~(second bindings)]
        (if-let* ~(drop 2 bindings) ~then ~else)
        ~(if-not (second bindings) else))
     then)))

(defmacro ->map
  "create a map of the values with the names as keywords"
  [& ks]
  (zipmap (map keyword ks) ks))

(defn uuid [] (.toString (UUID/randomUUID)))

(defn map-kv [f coll] (reduce-kv (fn [m k v] (assoc m k (f v))) (empty coll) coll))

(defn str->int [s] (when s (Integer/parseInt s)))

(defn group-by-with-transducer [key-f xf data]
  (let [ff (memoize (fn [k] (xf conj)))
        r  (reduce (fn [m d]
                       (let [k (key-f d)
                             v (get m k [])]
                         (if (reduced? v)
                           m
                           (assoc m k ((ff k) v d)))))
                   data)]
    (into {}
          (map (fn [[k v]] [k ((ff k) (unreduced v))]))
          r)))

(defn write-transit [dir file-name file-type coll]
  (let [suffix {:json ".json" :json-verbose ".verbose.json" :msgpack ".mp"}]
    (with-open [out (jio/output-stream
                     (str dir "/" file-name (file-type suffix)))]
      (t/write (t/writer out file-type) coll))))

(defn read-transit [dir file-name file-type]
  (let [suffix {:json ".json" :json-verbose ".verbose.json" :msgpack ".mp"}]
    (with-open [in (jio/input-stream (str dir "/" file-name (file-type suffix)))]
      (t/read (t/reader in file-type)))))

(defn dir-file-list
  [directory name-pattern]
  (->> directory
       (jio/file)
       (file-seq)
       (filter #(re-find name-pattern (.getName ^File %)))))

(defn dups [seq]
  (for [[id freq] (frequencies seq)
        :when (> freq 1)]
    id))

(defn duplicates
  [data params]
  (->> data
       (map params)
       frequencies
       (filter #(> (int (second %)) 1))
       (map first)
       set))

(defn numeric? [s]
  (if-let [s (seq s)]
    (let [s (if (= (first s) \-) (next s) s)
          s (drop-while #(Character/isDigit ^Character %) s)
          s (if (= (first s) \.) (next s) s)
          s (drop-while #(Character/isDigit ^Character %) s)]
      (empty? s))))

(defn symmetric-difference [s1 s2]
  (set/union (set/difference s1 s2) (set/difference s2 s1)))

(defn lazy-file-lines [file]
  (letfn [(helper [^BufferedReader rdr]
            (lazy-seq
             (if-let [line (.readLine ^BufferedReader rdr)]
               (cons line (helper rdr))
               (do (.close rdr) nil))))]
    (helper (jio/reader file))))

(defn load-csv-data
  [file-name separator]
  (with-open [in (jio/reader file-name)]
    (doall (csv/read-csv in :separator separator))))

(defn save-csv-data
  [file-name data]
  (with-open [out (jio/writer file-name)]
    (csv/write-csv out data)))

(defn save-coll
  [file coll]
  (when (seq coll)
    (->> coll
         (interpose \newline)
         (apply str)
         (spit file))))

(defn third [coll] (nth coll 2))
(defn fourth [coll] (nth coll 3))
(defn fifth [coll] (nth coll 4))
(defn sixth [coll] (nth coll 5))
(defn seventh [coll] (nth coll 6))
(defn eighth [coll] (nth coll 7))
(defn ninth [coll] (nth coll 8))
(defn tenth [coll] (nth coll 9))

(defn slurp-from-classpath
  "Slurps a file from the classpath."
  [path]
  (or (some-> path
              jio/resource
              slurp)
      (throw (FileNotFoundException. path))))

(defn file-older-than-days?
  "returns TRUE if a file is older than a given number of days
  or if the file does not exist"
  [^long days ^String file]
  (let [file-msec (.getTime (Date. (.lastModified (File. file))))
        now-msec  (.getTime (Date.))
        days-msec (* days 86400000)]
    (if (> (- now-msec file-msec) days-msec) true false)))

(defn get-edn-data
  [file]
  (try
    (read-string (slurp file))
    (catch FileNotFoundException e#
      nil)))

(defn safe-delete [file-path]
  (if (.exists (jio/file file-path))
    (try
      (jio/delete-file file-path)
      (catch Exception e (str "exception: " (.getMessage e))))
    false))

(defn delete-directory-contents [directory-path]
  (let [directory-contents (file-seq (jio/file directory-path))
        files-to-delete    (filter #(.isFile ^File %) directory-contents)]
    (doseq [file files-to-delete]
      (safe-delete (.getPath ^File file)))))

(defn delete-directory [directory-path]
  (do (delete-directory-contents directory-path)
      (safe-delete directory-path)))

(defn case-insensitive-compare [a b]
  (cond
    (and (nil? a) (nil? b)) 0
    (nil? a) 1
    (nil? b) -1
    :else (compare (str/upper-case a) (str/upper-case b))))

(defn set-ci
  ([] (sorted-set-by case-insensitive-compare))
  ([& keys] (apply sorted-set-by case-insensitive-compare keys)))

(defn map-ci
  ([] (sorted-map-by case-insensitive-compare))
  ([& keyvals] (apply sorted-map-by case-insensitive-compare keyvals)))

(def sort-distinct (comp sort distinct))

(defn first-char-uppercase? [s]
  (let [first-char (str (first s))]
    (re-find #"\p{Upper}" first-char)))

(defn first-char-numeric? [s]
  (numeric? (str (first s))))

(defn replace-several
  [str & replacements]
  (reduce (fn [s [a b]]
              (str/replace s a b))
          str
          (partition 2 replacements)))

(defn mapmap
  "Apply kf and vf to a sequence, s, and produce a map of (kf %) to (vf %)."
  ([vf s]
   (mapmap identity vf s))
  ([kf vf s]
   (zipmap (map kf s)
           (map vf s))))

(defn deep-merge
  "Like merge, but merges maps recursively."
  [& maps]
  (if (every? map? maps)
    (apply merge-with deep-merge maps)
    (last maps)))

(defn deep-merge-with
  "Like merge-with, but merges maps recursively, applying the given fn
  only when there's a non-map at a particular level."
  [f & maps]
  (apply
   (fn m [& maps]
       (if (every? map? maps)
         (apply merge-with m maps)
         (apply f maps)))
   maps))

(defn coerce-unformattable-types [args]
  (map (fn [x]
           (cond (instance? BigInt x) (biginteger x)
                 (instance? Ratio x) (double x)
                 :else x))
       args))

(defn format-plus [fmt & args]
  (apply format fmt (coerce-unformattable-types args)))

(defn any->binary [x] (if (contains? #{0 false "FALSE"} x) 0 1))
(defn any->bool [x] (if (= (any->binary x) 1) true false))

(defn avg-rd [avg i x] (float (+ avg (/ (- x avg) (inc i)))))

(defn assoc-in*
  "Associates value(s) in a nested associative structure, where ks is a
  sequence of keys and v is the new value and returns a new nested structure.
  If any levels do not exist, hash-maps will be created."
  ([m [k & ks] v]
   (if ks
     (assoc m k (assoc-in (get m k) ks v))
     (assoc m k v)))
  ([m ks v & kvs]
   (let [ret (assoc-in m ks v)]
     (if kvs
       (if (next kvs)
         (recur ret (first kvs) (second kvs) (nnext kvs))
         (throw (IllegalArgumentException.
                 "assoc-in expects an even number of arguments after map, found odd number")))
       ret))))


;(def r (java.util.Random. 42))
;
;(c/view
; (c/xy-chart
;  {"Mime" {:x (range 10)
;           :y (mapv #(+ % (* 3 (.nextDouble r))) (range 10))}
;   "Tyrone" {:x (range 10)
;             :y (mapv #(+ 2 % (* 4 (.nextDouble r)))
;                      (range 0 5 0.5))}}
;  {:title "Longest running distance"
;   :x-axis {:title "Months (since start)"}
;   :y-axis {:title "Distance"
;            :decimal-pattern "##.## km"}
;   :theme :matlab}))

(defn nill-safe [f & args] (when (every? some? args) (apply f args)))

;(defn reduce-xf [f init]
;  (fn [rf]
;    (let [acc (volatile! init)]
;      (completing (fn [result input] (rf result (vswap! acc f input)))))))
;
;(defn reduce-chan-with-state [f init]
;  (let [c (async/chan 1 (reduce-xf f init))]
;    (async/go-loop [v (<! c)] (when v (println (str v)) (recur (<! c))))
;    (async/onto-chan c (range 100))))

(def msg-str
  (str "01101001001000000110011001110101011000110110101101100101011001000010"
       "00000111100101101111011101010111001000100000011011010110111101101101"
       "00001101000010100110000101101110011001000010000001101110011011110111"
       "01110010000001100110011011110111001000100000011110010110111101110101"))

;(->> msg-str
;    ;(clojure.string/split #""))
;    (partition 8))


(defn poly-eval [poly val]
  (letfn [(term-rf [acc k v] (+ acc (* v (math/expt val k))))]
    (reduce-kv term-rf 0 poly)))

(defn lazy-pad
  "Returns a lazy sequence which pads sequence with pad-value."
  [sequence pad-value]
  (if (empty? sequence)
    (repeat pad-value)
    (lazy-seq (cons (first sequence) (lazy-pad (rest sequence) pad-value)))))

(defn zero-pad [seq num]
  (take num (lazy-pad seq 0)))

(defn same-size [a b]
  (let [max-size (max (count a) (count b))]
    [(zero-pad a max-size) (zero-pad b max-size)]))

(defn poly-fn [f]
  (fn [a b]
      (let [[a* b*] (same-size a b)]
        (mapv f a* b*))))

(def poly-add (poly-fn +))
(def poly-sub (poly-fn -))

(defn exp
  "eponential function e^x"
  [x]
  (math/expt 2.718 x))

(defn pinv
  "moore-penrose psuedo inverse using QR decomposition"
  [m]
  (let [{:keys [Q R]} (ml/qr m)
        n (m/column-count m)
        Q1' (m/transpose (m/submatrix Q [nil [0 n]]))
        R1+ (m/inverse (m/submatrix R [[0 n] nil]))]
    (m/mmul R1+ Q1')))

(defn least-squares
  "least squares solver using moore-penrose psuedo inverse to solve
  the overdetermined (n>m) linear system Ax=B"
  [A B]
  (m/mmul (pinv A) B))

(defn fo-step
  "first order step response"
  [m]
  (let [{:keys [tmax tsamp k tau step]} m
        n (inc (/ tmax tsamp))
        t (range 0 tmax tsamp)
        u (repeat n step)
        f (fn [t] (-> (* -1 t) (/ tau) (exp) (* -1) (+ 1) (* k step)))
        y (map f t)]
    (->map t u y)))

(defn arx
  "first order autoregressive (AR) model (na=1, nb=1),
  using least squares for parameter estimation"
  [m]
  (let [{:keys [t u y]} m
        A (m/transpose (m/matrix [(butlast y) (butlast u)]))
        B (m/matrix (rest y))
        X (least-squares A B)]
    (->map t u y X)))

(defn plot3 [m]
  "plot the response from the model vs the least squares solution"
  (let [{:keys [t u y y*]} m]
    (chart/view
     (chart/xy-chart
      {"SIM"  {:x t :y (butlast y*) :style {:marker-color :red :line-style :none}}
       "MEAS" {:x t :y y :style {:line-color :blue :marker-type :none}}
       "OUT"  {:x t :y u :style {:line-color :black :marker-type :none}}}
      {:title "First Order Response AR Simulation"
       :x-axis {:title "Time (sec)"}
       :y-axis {:title "% Change"}
       :theme :matlab}))))

(defn plot2 [m]
  "plot the response from the model"
  (let [{:keys [t x1 x2]} m]
    (chart/view
     (chart/xy-chart
      {"X1" {:x t :y x1 :style {:marker-type :none}}
       "X2" {:x t :y x2 :style {:marker-type :none}}}
      {:title "Response"
       :x-axis {:title "Time (sec)"}
       :y-axis {:title "% Change"}
       :theme :matlab}))))

(defn plot1 [m]
  "plot the response from the model"
  (let [{:keys [t x]} m]
    (chart/view
     (chart/xy-chart
      {"X" {:x t :y x :style {:line-color :red :marker-type :none}}}
      {:title "Response"
       :x-axis {:title "Time (sec)"}
       :y-axis {:title "% Change"}
       :theme :matlab}))))

(defn simulate [data]
  (let [{:keys [u X t y]} data
        a1 (first X)
        b1 (second X)
        y* (reduce
            (fn [y u] (conj y (+ (* a1 (last y)) (* b1 u))))
            [0]
            u)]
    (->map t y y* u)))


(defn ifft [t sigma delta f]
  (fn [sum wi]
    (let [witi (c/complex 0 (* wi t))
          wfti (c/complex 0 (* (+ wi delta) t))
          fi    (c/real-part (c/* (c/exp witi) (f (c/complex sigma wi))))
          ff    (c/real-part (c/* (c/exp wfti) (f (c/complex sigma (+ wi delta)))))]
      (+ sum (* 0.5 delta (+ fi ff))))))

(defn inverse-laplace
  [f sigma t]
  (let [nint 500
        delta 0.01]
    (-> (* sigma t)
        (exp)
        (* (reduce (ifft t sigma delta f) 0 (range 0 nint delta)))
        (/ 3.14159))))

(defn ifftm [t sigma delta f]
  (fn [sum wi]
      (let [witi (c/complex 0 (* wi t))
            wfti (c/complex 0 (* (+ wi delta) t))
            fi    (c/real-part (c/* (c/exp witi) (m/emap #(f (c/complex sigma %)) wi)))
            ff    (c/real-part (c/* (c/exp wfti) (f (c/complex sigma (+ wi delta)))))]
        (+ sum (* 0.5 delta (+ fi ff))))))

(m/set-current-implementation :persistent-vector)

(defn huddleston
  [f sigma t]
  (let [nint 500
        delta 0.01
        w1 (m/array (range 0 nint delta))
        w1t (m/mul w1 t)
        w2 (m/add w1 delta)
        witi (m/emap #(c/exp (c/complex 0 %)) (m/mul wi t))
        wfti (m/emap #(c/exp (c/complex 0 %)) (m/mul (m/add wi delta) t))]


    (-> (* sigma t)
        (exp)
        (* (reduce (ifft t sigma delta f) 0 (range 0 nint delta)))
        (/ 3.14159))))

(defn step [m]
  (let [defaults {:tmax 5 :tsamp 0.1 :sigma 0.1}
        params (merge defaults m)
        {:keys [tmax tsamp fy fu sigma]} params
        t (range 0 tmax tsamp)
        ys (fn [s] (c/* (c// s) (fy s)))
        us (fn [s] (c/* (c// s) (fu s)))
        y (map #(inverse-laplace ys sigma %) t)
        u (map #(inverse-laplace us sigma %) t)]
    (->map t y u)))


;(m/set-current-implementation :ndarray)


(defn pid [p i d]
  (let [Kc (c// 100 p)
        Ti (c/* i 60)
        Td (c/* d 60)]
    (fn [s] (c/+ Kc (c// Kc (c/* s Ti)) (c/* 0.1 Kc s Td)))))

(defn pi [p i]
  (let [Kc (c// 100 p)
        Ti (c/* i 60)]
    (fn [s] (c/+ Kc (c// Kc (c/* s Ti))))))

(defn ps [s] (c// (c/+ s 1)))
(def cs (pi 50 0.05))
(defn open-loop [s] (c/+ 1 (c/* (cs s) (ps s))))
(defn y-spt [s] (c// (c/* (cs s) (ps s)) (open-loop s)))
(defn u-spt [s] (c// (cs s) (open-loop s)))
(defn y-dist [s] (c// (ps s) (open-loop s)))
(defn u-dist [s] (c// (c/* -1 (ps s) (cs s)) (open-loop s)))

(defn model [process]
  (let [p (merge {:tmax 5 :tsamp 0.1 :sigma 0.01} process)]
    (-> p
        step
        arx
        simulate
        plot3)))

;(time (model {:fy y-spt :fu u-spt :tmax 15}))