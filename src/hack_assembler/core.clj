(ns hack-assembler.core
  (:import (clojure.lang IPersistentVector)))

(defprotocol SymbolTable
  (referenced? [this symbol])
  (get-symbol-address [this symbol])
  (reference-symbol [this symbol])
  (affect-symbol [this symbol address])
  (compute-nil-addresses [this]))

(def ^:static predefined-symbols
  [["SP" 0]
   ["LCL" 1]
   ["ARG" 2]
   ["THIS" 3]
   ["THAT" 4]
   ["R0" 0]
   ["R1" 1]
   ["R2" 2]
   ["R3" 3]
   ["R4" 4]
   ["R5" 5]
   ["R6" 6]
   ["R7" 7]
   ["R8" 8]
   ["R9" 9]
   ["R10" 10]
   ["R11" 11]
   ["R12" 12]
   ["R13" 13]
   ["R14" 14]
   ["R15" 15]
   ["SCREEN" 16384]
   ["KBD" 24576]])

(def ^:static userspace-vars 16)

(def ^:static dest-mnemonic
  {\A  2r100
   \D  2r010
   \M  2r001
   nil 2r000})

(def ^:static comp-mnemonic
  {"0"   2r101010
   "1"   2r111111
   "-1"  2r111010
   "D"   2r001100
   "A"   2r110000
   "!D"  2r001101
   "!A"  2r110001
   "-D"  2r001111
   "-A"  2r110011
   "D+1" 2r011111
   "A+1" 2r110111
   "D-1" 2r001110
   "A-1" 2r110010
   "D+A" 2r000010
   "D-A" 2r010011
   "A-D" 2r000111
   "D&A" 2r000000
   "D|A" 2r010101})

(def ^:static jump-mnemonic
  {"JGT" 2r001
   "JEQ" 2r010
   "JGE" 2r011
   "JLT" 2r100
   "JNE" 2r101
   "JLE" 2r110
   "JMP" 2r111
   nil   2r000})

(def ^:static C-INSTR-MASK 2r1110000000000000)

(def ^:static A-MASK 2r0001000000000000)

(defn replace-nil-address [{:keys [symbols var-count] :as ctx}
                           [symb address :as symbol-def]]
  (if address
    (assoc ctx :symbols (conj symbols symbol-def))
    (assoc ctx :symbols (conj symbols [symb (+ userspace-vars var-count)])
               :var-count (inc var-count))))

(defn index-where
  ([v pred]
   {:post [(or (nil? %)
               (and (not (neg? %))
                    (pred (get v %))))]}
   (loop [v v i 0]
     (if (empty? v)
       nil
       (if (pred (first v))
         i
         (recur (rest v) (inc i)))))))

(extend-type IPersistentVector
  SymbolTable
  (referenced? [this symbol]
    (some #(when (= symbol (first %)) true) this))

  (get-symbol-address [this symbol]
    (some #(when (= symbol (first %)) (second %)) this))

  (reference-symbol [this symbol]
    (if (referenced? this symbol)
      this
      (conj this [symbol nil])))

  (affect-symbol [this symbol address]
    (if-let [symb-index (index-where this #(= symbol (first %)))]
      (assoc this symb-index [symbol address])
      (conj this [symbol address])))

  (compute-nil-addresses [this]
    (-> (reduce replace-nil-address {:symbols [] :var-count 0} this)
        :symbols)))

(defrecord IndexMappedSymbolTable [index-map table]
  SymbolTable
  (referenced? [_ symbol]
    (contains? index-map symbol))

  (get-symbol-address [_ symbol]
    (->> (index-map symbol)
         (get table)
         second))

  (reference-symbol [this symbol]
    (if (referenced? this symbol)
      this
      (->IndexMappedSymbolTable
        (assoc index-map symbol (count table))
        (conj table [symbol nil]))))

  (affect-symbol [_ symbol address]
    (if-let [symb-index (index-map symbol)]
      (->IndexMappedSymbolTable index-map (assoc table symb-index [symbol address]))
      (->IndexMappedSymbolTable
        (assoc index-map symbol (count table))
        (conj table [symbol address]))))

  (compute-nil-addresses [_]
    (->IndexMappedSymbolTable
      index-map
      (-> (reduce replace-nil-address {:symbols [] :var-count 0} table)
          :symbols))))

(defn ->symbol-table [predefined-symbols]
  (reduce (fn [symb-table [symb address]]
            (affect-symbol symb-table symb address))
          (->IndexMappedSymbolTable {} [])
          predefined-symbols))

(defn remove-spaces [s]
  (clojure.string/replace s #"\s" ""))

(defn format-statement [line]
  (->> (remove-spaces line)
       (re-matches #"^([^/]+)(?://)?.*$")
       second))

(def user-symbol? (partial re-matches #"^[^\d](?:[\p{Alnum}_\.$:]*)"))

(defn symb-context [symbols next-pc]
  {:symbols symbols
   :next-pc next-pc})

(defn s->int [s] (Integer/parseInt s))

;; TODO use multimethod
(def parsers
  [{:matcher   #"@(.+)"
    :statement (fn [{:keys [symbols]} [symb]]
                 (let [address (or (get-symbol-address symbols symb) (s->int symb))]
                   {:type    :A_INSTRUCTION
                    :address address}))
    :symbols   (fn [{:keys [symbols next-pc]} [symb]]
                 (if (user-symbol? symb)
                   (symb-context (reference-symbol symbols symb) (inc next-pc))
                   (symb-context symbols (inc next-pc))))}  ;; TODO SRP

   {:matcher   #"([^=]+)=(.+)"
    :statement (fn [_ [dest comp]]
                 {:type :C_INSTRUCTION
                  :dest dest
                  :comp comp})
    :symbols   (fn [{:keys [symbols next-pc]} _]
                 (symb-context symbols (inc next-pc)))}

   {:matcher   #"^\(.+\)$"
    :statement (constantly nil)
    :symbols   (fn [{:keys [symbols next-pc]} [symb]]
                 (symb-context (affect-symbol symbols symb next-pc) next-pc))}

   {:matcher   #"([^;]+);(J\p{Upper}{2})"
    :statement (fn [_ [comp jump]]
                 {:type :J_INSTRUCTION
                  :comp comp
                  :jump jump})
    :symbols   (fn [{:keys [symbols next-pc]} _]
                 (symb-context symbols (inc next-pc)))}])


(defn parse [context statement kind]
  (let [[parser args] (some (fn [{:keys [matcher] :as parser}]
                              (when-let [[_ & parts] (re-matches matcher statement)]
                                [parser [context parts]]))
                            parsers)]
    (-> (kind parser)
        (apply args))))

(defn parse-statements [{:keys [statements] :as context} line]
  (if-let [statement (parse context line :statement)]
    (assoc-in context [:statements] (conj statements statement))
    context))

(defn parse-symbols [context line]
  (or (parse context line :symbols) context))

(defn comp->mnemonic [comp]
  (-> (or (comp-mnemonic comp) (comp-mnemonic (.replace comp \M \A)))
      (bit-shift-left 6)))

(defn dest->mnemonic [mask dest]
  (-> (dest-mnemonic dest)
      (bit-or mask)))

(defn assemble-c [comp dest jump]
  (let [dest (-> (reduce dest->mnemonic 0 dest) (bit-shift-left 3))
        a (if (.contains comp "M") A-MASK 0)
        comp (comp->mnemonic comp)
        jump (jump-mnemonic jump)]
    (bit-or C-INSTR-MASK a dest comp jump)))

(defmulti assemble :type)

(defmethod assemble :J_INSTRUCTION [{:keys [comp jump]}]
  (assemble-c comp "" jump))

(defmethod assemble :A_INSTRUCTION [{address :address}]
  {:pre [(integer? address)]}
  address)

(defmethod assemble :C_INSTRUCTION [{:keys [dest comp]}]
  (assemble-c comp dest nil))

(defn pad16-left0 [s]
  (str (reduce str (repeat (- 16 (count s)) "0")) s))

(defn int->2rstring [i]
  (-> (Integer/toString i 2)
      pad16-left0))

(defn asm-file->hack-file [asm-file]
  (let [[_ path name] (re-matches #"(.*/)(\w+).asm" asm-file)]
    (str path name ".hack")))

(defn write-hack-file [asm-file content]
  (spit (asm-file->hack-file asm-file) content))


(defn phase1 [lines]
  (->> (reduce parse-symbols {:symbols (->symbol-table predefined-symbols), :next-pc 0} lines)
       :symbols
       compute-nil-addresses))

(defn phase2 [asm-file lines symbols]
  (->> lines
       (reduce parse-statements {:statements []
                                 :symbols    symbols})
       :statements
       (map assemble)
       (map int->2rstring)
       (clojure.string/join "\n")
       (write-hack-file asm-file)))

(defn assembler [asm-file]
  (with-open [rdr (clojure.java.io/reader (clojure.java.io/file asm-file))]
    (let [lines (->> (line-seq rdr)
                     (map format-statement)
                     (filter (comp not nil?)))
          symbols (phase1 lines)]
      (phase2 asm-file lines symbols))))

(assembler "/home/stup3fait/bin/nand2tetris/projects/06/add/Add.asm")
(assembler "/home/stup3fait/bin/nand2tetris/projects/06/max/Max.asm")
(time (assembler "/home/stup3fait/bin/nand2tetris/projects/06/pong/Pong.asm"))
