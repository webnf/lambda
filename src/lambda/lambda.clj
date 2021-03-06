(ns lambda.interpreter
  (:require [clojure.walk :as walk]
            [clojure.java.io :as io]
            [clojure.edn :as edn]))

(def unevaluated (Object.))
(def unevaluated? #(identical? unevaluated %))
(def evaluated? (complement unevaluated?))
(declare ap? lambda?)

(defprotocol Thunk
  (normal? [t] "Do any more reduction rules apply to the thunk")
  (head-normal? [t] "Do any more reduction rules apply to the head of the thunk")
  (free-variables [t] "Get a collection of free variables from the thunk")
  (substitution [t v e] "Rename any bound occurrence of variable")
  (reduction [t] "Calculate a reduction step"))

(defprotocol Dbg
  (fv [_]))

(deftype Ap [f arg normal-form
             ^:unsynchronized-mutable __free_variables]
  Object
  (toString [_]
    (str "(" f " " arg ")"))
  Dbg
  (fv [_] __free_variables)
  Thunk

  (normal? [_] normal-form)
  (head-normal? [_] (and (not (lambda? f))
                         (head-normal? f)))

  (free-variables [_]
    (when (unevaluated? __free_variables)
      (set! __free_variables
            (into (free-variables f)
                  (free-variables arg))))
    __free_variables)

  (substitution [self v e]
    (let [fv (free-variables self)]
      (if (contains? fv v)
        (Ap. (substitution f v e)
             (substitution arg v e)
             false
             unevaluated)
        self)))

  (reduction [self]
    (cond
      (lambda? f)
                                        ; β-reduction
      (substitution
       (.-body f)
       (.-arg f)
       arg)

      (not (normal? f))
      (Ap. (reduction f)
           arg
           false unevaluated)

      (not (normal? arg))
      (Ap. f
           (reduction arg)
           false unevaluated)

      :else (Ap. f arg true unevaluated))))

(deftype Lambda [arg body normal-form
                 ^:unsynchronized-mutable __free_variables]
  Object
  (toString [_]
    (str "#λ[" arg " . " body "]"))
  Dbg
  (fv [_] __free_variables)

  Thunk

  (normal? [_] normal-form)
  (head-normal? [_] (head-normal? body))

  (free-variables [_]
    (when (unevaluated? __free_variables)
      (set! __free_variables
            (disj (free-variables body) arg)))
    __free_variables)

  (substitution [self v e]
    (let [fv (free-variables self)]
      (if (contains? fv v)
                                        ; α-conversion
        (if (contains? (free-variables e) arg)
          (let [new-arg (gensym (str arg))]
            (Lambda. new-arg
                     (-> body
                         (substitution arg new-arg)
                         (substitution v e))
                     false
                     unevaluated))
          (Lambda. arg
                   (substitution body v e)
                   false
                   unevaluated))
        self)))

  (reduction [self]
    (let [body (reduction body)]
      (if (normal? body)
        (if (and (ap? body)
                 (= arg (.-arg body))
                 (not (contains? (free-variables (.-f body))
                                 arg)))
                                        ; η-conversion
          (.-f body)
          (Lambda. arg body true unevaluated))
        (Lambda. arg body false unevaluated)))))

(def lambda? #(instance? Lambda %))
(def ap? #(instance? Ap %))

(def atom-impl
  {:normal? (fn [_] true)
   :head-normal? (fn [_] true)
   :free-variables (fn [sym] #{sym})
   :substitution (fn [sym v e]
                   (if (= sym v)
                     e sym))
   :reduction (fn [sym] sym)})

(extend clojure.lang.Symbol
  Thunk atom-impl)
(extend clojure.lang.Keyword
  Thunk atom-impl)
(extend java.lang.Boolean
  Thunk atom-impl)
(extend java.lang.String
  Thunk atom-impl)
(extend java.lang.Number
  Thunk atom-impl)

(declare embed)

(defmacro ap [head & args]
  (if (seq args)
    (let [h `(Ap. ~(embed head) ~(embed (first args))
                  false unevaluated)]
      (if (seq (rest args))
        `(ap ~h ~@(rest args))
        h))
    (embed head)))

(defn embed [host-expr]
  (let [expr (walk/macroexpand-all host-expr)]
    (cond (symbol? expr)
          (list 'quote expr)
          (list? expr)
          `(ap ~@expr)
          :else
          expr)))

(defmacro lambda [arg & body]
  `(Lambda. '~arg (ap ~@body)
            false unevaluated))

(defmacro λ [arg dot-or-arg & body]
  {:pre [(not (empty? body))]}
  `(lambda ~arg ~@(if (= '. dot-or-arg)
                    body
                    [`(λ ~dot-or-arg ~@body)])))

(defmacro ap-file [filename]
  (cons `ap
        (with-open [rdr (java.io.PushbackReader. (io/reader filename))]
          (doall
           (take-while some?
                       (repeatedly
                        #(try (edn/read rdr)
                              (catch Exception _ nil))))))))

(defn eval-step [expr]
  (if (normal? expr)
    expr
    (reduction expr)))

(defn eval-steps [expr]
  (iterate eval-step expr))

(defn head-reduction [expr]
  (if (head-normal? expr)
    expr
    (recur (reduction expr))))

(defn full-reduction [expr]
  (if (normal? expr)
    expr
    (recur (reduction expr))))

(defn thunk-apply [f arg]
  (Ap. f arg false unevaluated))

(def stdenv (time (head-reduction (ap-file "./src/lambda/core.rlj"))))
(defmacro with-stdenv [& expr]
  `(thunk-apply
    stdenv
    (λ ~@'[id Y Z true false ap and or inc normal-not pair * exp right-fold-cons
           0 + zero? dec if not fst snd pair-nil pair-cons right-fold-nil right-fold-nil? right-fold-head right-fold-tail
           1 xor - pair-nil? pair-head pair-tail
           2 div1
           3 / .]
       ~@expr)))

#_ (time (full-reduction prog))
#_(time (head-reduction prog))

(str
 (head-reduction
  (with-stdenv
    + 1 2)))

(do
 (def state
   (atom (with-stdenv

           (pair-head (pair-cons 2 (pair-cons 1 pair-nil)))
           #_Y

           #_(/ ((right-fold-cons 3 (right-fold-cons 2 (right-fold-cons 1 right-fold-nil)))
                 * 3)
                1)
           #_(-  (* (inc (inc 0))
                    (inc (inc 0)))
                 (inc (inc 0)))
           #_(- (* (inc (inc (inc 0)))
                   (inc (inc 0)))
                (inc (inc (inc 0))))
           #_(/ (inc (inc (inc (inc (inc (inc 0))))))
                (inc (inc (inc 0))))
           #_(inc (inc 0))
           #_(inc 0)
           #_0
           #_(/ (λ f x . f (f (f (f (f (f (f (f (f x)))))))))
                (λ f x . f (f (f x))))
           #_(inc (inc (inc 0)))
           #_(* (inc 0) (inc (inc (inc 0))))
           #_(* (inc (inc 0))
                (inc (inc (inc 0))))
           #_(inc inc (inc 0))
           #_inc #_0)))

 (time
  (while (not (head-normal? @state))
    (swap! state reduction)))
 (println (str @state))
 @state)


