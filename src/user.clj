(ns user
  (:require
   [clojure.main]
   [clojure.java.io :as jio]
   [clojure.core.reducers :as r]
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
   [cquad.core :as cquad]
   [util.core :as util]
   [clojure.core.matrix.protocols :as mp])
   ;[infix.core :refer [base-env]]
   ;[infix.math :refer [defbinary]]
   ;[infix.macros :refer [infix from-string]]
   ;[mikera.cljutils.loops :as loops])
  (:import
   (java.io File FileNotFoundException Reader BufferedReader)
   (java.util Date UUID)
   (clojure.lang BigInt Ratio)
   (org.apache.commons.math3.complex Complex ComplexField)
   (org.apache.commons.math3.linear ArrayFieldVector)))


(set! *warn-on-reflection* true)
(set! *unchecked-math* true)


;(defn tuple->complex [[real imag]]
;  (Complex. real imag))
;
;(defn complex->tuple [x]
;  [(c/real-part x) (c/imaginary-part x)])
;
;
;(defn addv ^ArrayFieldVector [^ArrayFieldVector a ^ArrayFieldVector b]
;  (.add a b))
;
;(defn subv ^ArrayFieldVector [^ArrayFieldVector a ^ArrayFieldVector b]
;  (.subtract a b))
;
;(defn divv ^ArrayFieldVector [^ArrayFieldVector a ^ArrayFieldVector b]
;  (.ebeDivide a b))
;
;(defn mulv ^ArrayFieldVector [^ArrayFieldVector a ^ArrayFieldVector b]
;  (.ebeMultiply a b))
;
;(defn addc ^ArrayFieldVector [^ArrayFieldVector a ^Complex b]
;  (.mapAdd a b))
;
;(defn subc ^ArrayFieldVector [^ArrayFieldVector a ^Complex b]
;  (.mapSubtract a b))
;
;(defn divc ^ArrayFieldVector [^ArrayFieldVector a ^Complex b]
;  (.mapDivide a b))
;
;(defn mulc ^ArrayFieldVector [^ArrayFieldVector a ^Complex b]
;  (.mapMultiply a b))
;
;(defn expv ^ArrayFieldVector [^ArrayFieldVector a]
;  (map c/exp a))
;
;(defn complex-vector [coll]
;  (ArrayFieldVector.
;   #^"[Lorg.apache.commons.math3.complex.Complex;"
;   (into-array
;    (map tuple->complex coll))))
;
;(defn avec-map->seq [f avec]
;  (map f (.getData ^ArrayFieldVector avec)))
;
;(defn amap->avec [f avec]
;  (ArrayFieldVector.
;   #^"[Lorg.apache.commons.math3.complex.Complex;"
;   (into-array (map f (.toArray ^ArrayFieldVector avec)))))
;
;(defn complex-tuples [avec]w
;  (avec-map->seq  complex->tuple avec))
;
;(defn real-parts [avec]
;  (avec-map->seq  c/real-part avec))
;
;(defn imaginary-parts [avec]
;  (avec-map->seq  c/imaginary-part avec))
;
;(def a (complex-vector [[1 2] [3 4]]))
;(complex-tuples (amap->avec c/exp a))
;
;;(def a (complex-array [(Complex. 1 2) (Complex. 2 4) (Complex. 3 5)]))
;;(def b (complex-array [(Complex. 1 2) (Complex. 2 4) (Complex. 3 5)]))
;;(addc a b)


;(def msg-str
;  (str "01101001001000000110011001110101011000110110101101100101011001000010"
;       "00000111100101101111011101010111001000100000011011010110111101101101"
;       "00001101000010100110000101101110011001000010000001101110011011110111"
;       "01110010000001100110011011110111001000100000011110010110111101110101"))

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

(defn arx
  "first order autoregressive (AR) model (na=1, nb=1),
  using least squares for parameter estimation"
  [m]
  (let [{:keys [t u y]} m
        A (m/transpose (m/matrix [(butlast y) (butlast u)]))
        B (m/matrix (rest y))
        X (least-squares A B)]
    (util/->map t u y X)))

;(defn arx
;  "first order autoregressive (AR) model (na=1, nb=1),
;  using least squares for parameter estimation"
;  [m]
;  (let [{:keys [t u y]} m
;        n (count t)
;        A (m/transpose (m/matrix [(subvec y 0 (- n 2))
;                                  (subvec y 1 (- n 1))
;                                  (subvec u 0 (- n 2))
;                                  (subvec u 1 (- n 1))]))
;        B (m/matrix (subvec y 2 n))
;        X (least-squares A B)]
;    (util/->map t u y X)))

;(defn arx
;  "first order autoregressive (AR) model (na=1, nb=1),
;  using least squares for parameter estimation"
;  [m]
;  (let [{:keys [t u y]} m
;        n (count t)
;        A (m/transpose (m/matrix [(subvec y 0 (- n 4))
;                                  (subvec y 1 (- n 3))
;                                  (subvec y 2 (- n 2))
;                                  (subvec y 3 (- n 1))
;                                  (subvec u 0 (- n 4))]))
;        B (m/matrix (subvec y 4 n))
;        X (least-squares A B)]
;    (util/->map t u y X)))

(defn plot3 [m]
  "plot the response from the model vs the least squares solution"
  (let [{:keys [t u y y*]} m]
    (chart/view
     (chart/xy-chart
      {"SIM"  {:x t :y y* :style {:marker-color :red :line-style :none}}
       "MEAS" {:x t :y y :style {:line-color :blue :marker-type :none}}
       "OUT"  {:x t :y u :style {:line-color :black :marker-type :none}}}
      {:title "First Order Response AR Simulation"
       :x-axis {:title "Time (sec)"}
       :y-axis {:title "% Change"}
       :theme :matlab}))))

(defn plot2 [m]
  "plot the response from the model"
  (let [{:keys [t y u]} m]
    (chart/view
     (chart/xy-chart
      {"y" {:x t :y y :style {:marker-type :none}}
       "u" {:x t :y u :style {:marker-type :none}}}
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

(defn huddleston
  [fs sigma t]
  (let [nint  500
        delta 0.01
        k     (/ (* (exp (* sigma t)) delta 0.5) 3.14159)
        f     (fn [i]
                  (c/real-part
                   (c/* (c/exp (c/complex 0 (* t i)))
                        (fs (c/complex sigma i)))))
        rf    (fn
               ([] 0)
               ([sum i] (+ sum (f i) (f (+ i delta)))))]
    (* k (r/fold + rf (vec (range 0 nint delta))))))

(defn zakian [fs t]
  (let [k [[(c/complex 12.83767675 1.666063445) (c/complex -36902.08210 196990.4257)]
           [(c/complex 12.22613209 5.012718792) (c/complex 61277.02524 -95408.62551)]
           [(c/complex 10.93430308 8.409673116) (c/complex -28916.56288 18169.18531)]
           [(c/complex 8.776434715 11.92185389) (c/complex 4655.361138 -1.901528642)]
           [(c/complex 5.225453361 15.72952905) (c/complex -118.7414011 -141.3036911)]]]
    (-> (reduce (fn [acc [k1 k2]] (+ acc (c/real-part (c/* k2 (fs (c// k1 t)))))) 0 k)
        (* 2)
        (/ t))))

(defn step [m]
  (let [{:keys [tmax tsamp fy fu]} m
        t  (vec (range 0.00000001 tmax tsamp))
        ys (fn [s] (c/* (c// s) (fy s)))
        us (fn [s] (c/* (c// s) (fu s)))
        y  (vec (map #(zakian ys %) t))
        u  (vec (map #(zakian us %) t))]
    (util/->map t y u)))

(defn pid [p i d]
  (let [Kc (c// 100 p)
        Ti (c/* i 60)
        Td (c/* d 60)
        n  0.1]
    (fn [s] (c/+ Kc (c// Kc (c/* s Ti)) (c// (c/* n Td) (c/+ 1 (c// n s)))))))

(defn pi [p i]
  (let [Kc (c// 100 p)
        Ti (c/* i 60)]
    (fn [s] (c/+ Kc (c// Kc (c/* s Ti))))))

(defn ps [s] (c// (c/+ s 1)))
;(defn ps [s] (c// 5 (c/* (c/+ s 1) (c/+ s 3) (c/+ s 2) (c/+ s 1))))
;(defn ps [s] (c// (c/* 3 (c/+ s 5)) (c/+ s 15)))
(def cs (pid 100 0.01 0.05))
(defn open-loop [s] (c/+ 1 (c/* (cs s) (ps s))))
(defn y-spt [s] (c// (c/* (cs s) (ps s)) (open-loop s)))
(defn u-spt [s] (c// (cs s) (open-loop s)))
(defn y-dist [s] (c// (ps s) (open-loop s)))
(defn u-dist [s] (c// (c/* -1 (ps s) (cs s)) (open-loop s)))

(defn simulate [data]
  (let [{:keys [u X t y]} data
        a1  (first X)
        b1  (second X)
        y** (reduce
             (fn [y u] (conj y (+ (* a1 (last y)) (* b1 u))))
             [0]
             u)
        n   (count t)]
    {:t  (subvec t 1 n)
     :u  (subvec u 1 n)
     :y  (subvec y 1 n)
     :y* (subvec y** 1 n)}))

;(defn simulate [data]
;  (let [{:keys [u X t y]} data
;        a1 (first X)
;        a2 (second X)
;        b1 (util/third X)
;        b2 (util/fourth X)
;        y** (reduce
;              (fn [acc uc]
;                  (let [y' (reverse (first acc))
;                        n (count y')
;                        y2 (if (>= n 2) (first y') 0)
;                        y1 (if (>= n 1) (second y') 0)
;                        u2 (if (>= n 1) (second acc) 0)
;                        z (+ (* a1 y1)
;                             (* a2 y2)
;                             (* b1 u2)
;                             (* b2 uc))]
;                    (conj (first acc) z)))
;              [[]]
;              u)
;        y* (first y**)]
;    (util/->map t y y* u)))

(defn model [process]
  (-> process
      step
      arx
      simulate
      plot3))

;(defn fy [s] (c// (c/* 0.17 (c/+ s 2.5) (c/+ s 4) (c/+ s 3.5)) (c/* (c/+ s 1) (c/+ s 3) (c/+ s 2) (c/+ s 1))))
;(defn fy [s] (c// (c/* 3 (c/+ s 5)) (c/+ s 15)))
(defn fy [s] (c// (c/+ s 1)))
(defn fu [s] 1)

(model {:fy y-spt :fu u-spt :tmax 5 :tsamp 0.1})

;(huddleston fs 0 0)
;(zakian fs 0.0000001)
