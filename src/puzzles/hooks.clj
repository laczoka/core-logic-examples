(ns puzzles.logic
" Using core.logic to solve an interesting puzzle
  See the puzzle description here: https://www.janestreet.com/puzzles/hooks-2/ 
  And the solution here: https://www.janestreet.com/puzzles/solutions/may-2016-solution/

  Not the most efficient or clever solution, 
  the emphasis was put on preserving readability and implementing the intuitive approach

  A specialized back-tracking search algo is way-way faster, however way less readable"

  (:refer-clojure :exclude [==])
  (:require [clojure.core.logic.fd :as fd]
            [clojure.core.logic :refer :all]))

(def +col-sum+    [36  5 47 35 17 30 21 49 45])
(def +row-sum+ [45                
                44
                4
                48
                7
                14
                47
                43
                33
                ])

(set! *warn-on-reflection* true)

 (defn sumo [vs sum]
     (fresh [sum' v rest-vs]
       (conde
        [(== sum 0) (== vs ())]
        [(conso v rest-vs vs)
         (fd/+ v sum' sum)
         (sumo rest-vs sum')])))

(defn- firstv [v]
  (when-not (empty? v)
    (v 0)))

(defn- lastv [v]
  (when-not (empty? v)
    (v (- (count v) 1))))

(defn- nextv [v]
  (when-not (< (count v) 2)
    (subvec v 1)))

(defn- butlastv [v]
  (when-not (< (count v) 2)
    (subvec v 0 (- (count v) 1))))


(defn se-rows [rows]
  (mapv nextv (nextv rows)))

(defn se-cols [cols]
  (mapv nextv (nextv cols)))

(defn sw-rows [rows]
  (mapv butlastv (nextv rows)))

(defn sw-cols [cols]
  (mapv nextv (butlastv cols)))

(defn nw-rows [rows]
  (mapv butlastv (butlastv rows)))

(defn nw-cols [cols]
  (mapv butlastv (butlastv cols)))

(defn ne-rows [rows]
  (mapv nextv (butlastv rows)))

(defn ne-cols [cols]
  (mapv butlastv (nextv cols)))

(defn hooko [rs cs rows cols]
  (let [l (count rows)
        rs' (vec (repeatedly (- l 1) lvar))
        cs' (vec (repeatedly (- l 1) lvar))]
    (conde
     ;; base case
     [(fresh [row col]
        (conso 1 () rs)
        (conso 1 () cs)

        (conso row () rows)
        (conso 1 () row)
        (conso col () cols)
        (conso 1 () col))]
     [;; place a NW oriented hook (0's and l number of l's) such that
      ;; constrain the number of l's
      (fresh [rc-sum]
        (fd/+ (firstv rs) (firstv cs) rc-sum)
        (fd/in rc-sum (fd/domain (* l l) (* l (+ l 1)))))
      ;; the hook's row adheres to the row sum
      (everyg #(fd/in % (fd/domain 0 l)) (firstv rows))
      (sumo (firstv rows) (firstv rs))
      ;; the hook's column adhere to the column sum
      (everyg #(fd/in % (fd/domain 0 l)) (firstv cols))
      (sumo (firstv cols) (firstv cs))
      ;; hook's row satisfies column sum constrains
      (everyg (fn [[r s s']] (fd/+ s' r s)) (map vector (nextv (firstv rows)) (nextv cs) cs'))
      (everyg #(fd/< 0 %) cs')
      ;; hook's column satisfies row sum constrains
      (everyg (fn [[r s s']] (fd/+ s' r s)) (map vector (nextv (firstv cols)) (nextv rs) rs'))
      (everyg #(fd/< 0 %) rs')
      
      (hooko rs' cs' (se-rows rows) (se-cols cols))]
     
     [;; place a NE oriented hook (0's and l number of l's) such that
      ;; constrain the number of l's
      (fresh [rc-sum]
        (fd/+ (firstv rs) (lastv cs) rc-sum)
        (fd/in rc-sum (fd/domain (* l l) (* l (+ l 1)))))
      ;; the hook's row adheres to the row sum
      (everyg #(fd/in % (fd/domain 0 l)) (firstv rows))
      (sumo (firstv rows) (firstv rs))
      ;; the hook's column adhere to the column sum
      (everyg #(fd/in % (fd/domain 0 l)) (lastv cols))
      (sumo (lastv cols) (lastv cs))
      ;; hook's row satisfies column sum constrains
      (everyg (fn [[r s s']] (fd/+ s' r s)) (map vector (butlastv (firstv rows)) (butlastv cs) cs'))
      (everyg #(fd/< 0 %) cs')
      ;; hook's column satisfies row sum constrains
      (everyg (fn [[r s s']] (fd/+ s' r s)) (map vector (nextv (lastv cols)) (nextv rs) rs'))
      (everyg #(fd/< 0 %) rs')
      
      (hooko rs' cs' (sw-rows rows) (sw-cols cols))]
     
     [;; place a SE oriented hook (0's and l number of l's) such that
      ;; constrain the number of l's
      (fresh [rc-sum]
        (fd/+ (lastv rs) (lastv cs) rc-sum)
        (fd/in rc-sum (fd/domain (* l l) (* l (+ l 1)))))
      ;; the hook's row adheres to the row sum
      (everyg #(fd/in % (fd/domain 0 l)) (lastv rows))
      (sumo (lastv rows) (lastv rs))
      ;; the hook's column adhere to the column sum
      (everyg #(fd/in % (fd/domain 0 l)) (lastv cols))
      (sumo (lastv cols) (lastv cs))
      ;; hook's row satisfies column sum constrains
      (everyg (fn [[r s s']] (fd/+ s' r s)) (map vector (butlastv (lastv rows)) (butlastv cs) cs'))
      (everyg #(fd/< 0 %) cs')
      ;; hook's column satisfies row sum constrains
      (everyg (fn [[r s s']] (fd/+ s' r s)) (map vector (butlastv (lastv cols)) (butlastv rs) rs'))
      (everyg #(fd/< 0 %) rs')
      
      (hooko rs' cs' (nw-rows rows) (nw-cols cols))]
     
     [;; place a SW oriented hook (0's and l number of l's) such that
      ;; constrain the number of l's
      (fresh [rc-sum]
        (fd/+ (last rs) (first cs) rc-sum)
        (fd/in rc-sum (fd/domain (* l l) (* l (+ l 1)))))
      ;; the hook's row adheres to the row sum
      (everyg #(fd/in % (fd/domain 0 l)) (last rows))
      (sumo (last rows) (last rs))
      ;; the hook's column adhere to the column sum
      (everyg #(fd/in % (fd/domain 0 l)) (first cols))
      (sumo (first cols) (first cs))
      ;; hook's row satisfies column sum constrains
      (everyg (fn [[r s s']] (fd/+ s' r s)) (map vector (next (last rows)) (next cs) cs'))
      (everyg #(fd/< 0 %) cs')
      ;; hook's column satisfies row sum constrains
      (everyg (fn [[r s s']] (fd/+ s' r s)) (map vector (butlast (first cols)) (butlast rs) rs'))
      (everyg #(fd/< 0 %) rs')
      
      (hooko rs' cs' (ne-rows rows) (ne-cols cols))])))


(defn solve [n row-sums col-sums]
  (let [l (count row-sums)
        vars (repeatedly (* l l) lvar)
        rows (into [] (map vec) (partition l vars))
        cols (vec (apply map vector rows))
        rs (vec (repeatedly l lvar))
        cs (vec (repeatedly l lvar))]
    (if (and (< n 1) (not= l (count cols)))
      (list) ;; -> invalid input     
      ;; else solve
      (->> (run n [q]
             (== row-sums rs)
             (== col-sums cs)
             
             (hooko rs cs rows cols)

             (== q vars))
           (map #(partition l %))))))

(defn print-sq [rows]
  (doseq [r rows]
    (println r)))

(defn products [rows]
  (let [l (count rows)
        selected (repeatedly l lvar)
        domains (for [r rows]
                  (filter #(not= 0 (nth r %)) (range l)))]
    ;; domains
      (->> (run* [q]
             (everyg (fn [[s d]] (fd/in s (apply fd/domain d))) (map vector selected domains))
             (fd/distinct q)
             (== q selected))
           
           (map #(apply * (map nth rows %)))
           )))

(defn find-max [products]
  (apply max products))

(defn run-solver []
  (let [[solution-rows :as solutions] (solve 2 +row-sum+ +col-sum+)]
    (println "Solution:")
    ;; solve and check if there is indeed only one solution
    (doseq [s solutions] (print-sq s))    
    ;; Solution: 
    ;; ( 9 0 9 0 0|9|0 9 9 )
    ;; ( 0 0 5 5 5 5 7 8|9|)
    ;; ( 0 0 0|4|0 0 0 0 0 )
    ;; ( 6 5 4 3 3 3|7|8 9 )
    ;; ( 0 0|4|2 1 0 0 0 0 )
    ;; ( 0 0 4 0 2 0 0|8|0 )
    ;; ( 6 0 6 6|6|6 0 8 9 )
    ;; ( 7 0 7|7|0 7 7 8 0 )
    ;; (|8|0 8 8 0 0 0 0 9 )
    (println)
    (println "Max product:" (find-max (products solution-rows)))))

(comment
  (time (run-solver))
  )
