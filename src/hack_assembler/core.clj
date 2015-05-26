(ns hack-assembler.core)

(defn- remove-spaces [s]
  (clojure.string/replace s #"\s" ""))

(defn index-where                                           ;;TODO move to util.vector
  ([v pred] (index-where v pred 0))
  ([v pred i]
   (if (empty? v)
     nil
     (if (pred (first v))
       i
       (recur (rest v) pred (inc i))))))

(defn replacev-at [v i val]                                 ;;TODO move to util.vector
  (into (conj (subvec v 0 i) val) (subvec v (inc i))))

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

(defn format-statement [line]
  (->> (remove-spaces line)
       (re-matches #"^([^/]+)(?://)?.*$")
       second))

(def user-symbol? (partial re-matches #"^[^\d](?:[\p{Alnum}_\.$:]*)"))

(defn referenced? [symbols symb]
  (some #(when (= symb (first %)) true) symbols))

(defn get-symbol-address [symbols symb]
  (some #(when (= symb (first %)) (second %)) symbols))

(defn reference-symbol                                      ;; TODO use protocol for symbol table ?
  [symbols symb]
  (if (referenced? symbols symb)
    symbols
    (conj symbols [symb nil])))

(defn affect-symbol
  [symbols symb address]
  (if-let [symb-index (index-where symbols #(= symb (first %)) 0)]
    (replacev-at symbols symb-index [symb address])
    (conj symbols [symb address])))

(defn replace-nil-address [{:keys [symbols var-count] :as ctx}
                           [symb address :as symbol-def]]
  (if address
    (assoc ctx :symbols (conj symbols symbol-def))
    (assoc ctx :symbols (conj symbols [symb (+ userspace-vars var-count)])
               :var-count (inc var-count))))

(defn compute-nil-addresses [symbols]
  (-> (reduce replace-nil-address {:symbols [] :var-count 0} symbols)
      :symbols))

(defn symb-context [symbols next-pc]
  {:symbols symbols
   :next-pc next-pc})

(defn s->int [s] (Integer/parseInt s))

;; TODO use multimethod
(def parsers
  [{:matcher   #(.startsWith % "@")
    :statement (fn [statement {:keys [symbols]}]
                 (let [symb (subs statement 1)
                       address (or (get-symbol-address symbols symb) (s->int symb))]
                   {:type    :A_INSTRUCTION
                    :address address}))
    :symbols   (fn [statement {:keys [symbols next-pc]}]
                 (let [symb (subs statement 1)]
                   (if (user-symbol? symb)
                     (symb-context (reference-symbol symbols symb) (inc next-pc))
                     (symb-context symbols (inc next-pc)))))} ;; TODO SRP

   {:matcher   #(.contains % "=")
    :statement (fn [statement _]
                 (let [[_ dest comp] (re-matches #"([^=]+)=(.+)" statement)]
                   {:type :C_INSTRUCTION
                    :dest dest
                    :comp comp}))
    :symbols   (fn [_ {:keys [symbols next-pc]}] (symb-context symbols (inc next-pc)))}

   {:matcher   #(re-matches #"^\(.+\)$" %)
    :statement (constantly nil)
    :symbols   (fn [statement {:keys [symbols next-pc]}]
                 (let [[_ symb] (re-matches #"^\((.+)\)$" statement)]
                   (symb-context (affect-symbol symbols symb next-pc) next-pc)))}

   {:matcher   #(re-matches #"[^;]+;J\p{Upper}{2}" %)
    :statement (fn [statement _]
                 (let [[_ comp jump] (re-matches #"([^;]+);(J\p{Upper}{2})" statement)]
                   {:type :J_INSTRUCTION
                    :comp comp
                    :jump jump}))
    :symbols   (fn [_ {:keys [symbols next-pc]}] (symb-context symbols (inc next-pc)))}])


(defn parse [context line kind]
  (when-let [statement (format-statement line)]
    (-> (filter (fn [{:keys [matcher]}] (matcher statement)) parsers)
        first
        kind
        (apply [statement context]))))

(defn parse-statements [{:keys [statements] :as context} line]
  (if-let [statement (parse context line :statement)]
    (assoc-in context [:statements] (conj statements statement))
    context))

(defn parse-symbols [context line]
  (println (count (:symbols context)) line)
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
  (->> (reduce parse-symbols {:symbols predefined-symbols, :next-pc 0} lines)
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
    (let [lines (vec (line-seq rdr))
          symbols (phase1 lines)]
      (phase2 asm-file lines symbols))))

#_(assembler "/home/stup3fait/bin/nand2tetris/projects/06/add/Add.asm")
#_(assembler "/home/stup3fait/bin/nand2tetris/projects/06/max/Max.asm")
(assembler "/home/jerome/bin/nand2tetris/projects/06/pong/Pong.asm")
