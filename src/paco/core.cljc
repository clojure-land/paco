(ns paco.core
  (:refer-clojure :exclude [* + char not sequence])
  (:require [clojure.core :as clojure]
            [clojure.set :as set]
            [clojure.spec :as spec]
            [clojure.string :as string]))

;; ---------------------------------------------------------------------
;; Protocols

(defprotocol IGetInput
  (-get-input [this]))

(defprotocol IGetState
  (-get-state [this]))

(defprotocol IGetValue
  (-get-value [this]))

(defprotocol IFmap
  (-fmap [this x]))

(defprotocol IPosition
  (-column [this])
  (-line [this])
  (-position [this])
  (-next-position [this char]))

;; ---------------------------------------------------------------------
;; Position API

(defn position?
  "true if `x` implements `IPosition`, false otherwise."
  [x]
  (satisfies? IPosition x))

(defn position
  "Return the position of `x`."
  [x]
  {:post [(position? %)]}
  (-position x))

(defn column [position]
  {:pre [(position? position)]
   :post [(integer? %)]}
  (-column position))

(defn line [position]
  {:pre [(position? position)]
   :post [(integer? %)]}
  (-line position))

(defn next-position [position char]
  {:pre [(position? position)]
   :post [(position? %)]}
  (-next-position position char))

(defn get-input [x]
  {:post [(clojure/or (string? %) (seq? %))]}
  (-get-input x))

(defn get-value [x]
  (-get-value x))

(defn get-state [x]
  (-get-state x))

(defn fmap [f x]
  (-fmap x f))

;; ---------------------------------------------------------------------
;; Position implementation

(defrecord Position [column line]
  IPosition
  (-column [this]
    column)

  (-line [this]
    line)

  (-next-position [this char]
    (if (clojure/or (= char \newline)
                    (= char \return))
      (map->Position {:column 1
                      :line (inc line)})
      (update this :column inc)))
  
  (-position [this]
    this))

;; ---------------------------------------------------------------------
;; Success implementation and API

(defrecord Success [state value]
  IFmap
  (-fmap [this f]
    (update this :value f))

  IGetState
  (-get-state [this]
    state)

  IGetValue
  (-get-value [this]
    value)

  IPosition
  (-column [this]
    (-column (-position this)))

  (-line [this]
    (-line (-position this)))

  (-position [this]
    (-position state)))

(defn make-success
  "Return an of `Success`."
  [value state]
  (map->Success {:state state
                 :value value}))

(defn success?
  "true if `x` is an instance of `Success`."
  [x]
  (instance? Success x))

;; ---------------------------------------------------------------------
;; Failure implementation and API

(defrecord Failure [labels message state]
  IFmap
  (-fmap [this f]
    this)

  IGetState
  (-get-state [this]
    state))

(defn failure?
  "true if x is an instance of `Failure`."
  [x]
  (instance? Failure x))

(defn make-failure
  "Return an of `Failure`."
  ([state message]
   (map->Failure {:labels #{}
                  :message message
                  :state state}))
  ([state message labels]
   {:pre [(set? labels)]}
   (map->Failure {:labels labels
                  :message message
                  :state state})))

(defn get-labels
  [failure]
  {:pre [(failure? failure)]
   :post [(set? %)]}
  (get failure :labels))

(defn set-labels
  [failure labels]
  {:pre [(failure? failure)
         (set? labels)]}
  (assoc failure :labels labels))

(defn update-labels
  [failure f & args]
  {:pre [(failure? failure)
         (fn? f)]}
  (let [labels (get-labels failure)
        new-labels (apply f labels args)]
    (set-labels failure new-labels)))

;; ---------------------------------------------------------------------
;; Parser implementation and API

(deftype Parser [parse-fn]
  
  clojure.lang.IFn
  (invoke [this state]
    (parse-fn state))

  IFmap
  (-fmap [this f]
    (Parser.
     (fn [state]
       (let [result (this state)]
         (fmap f result))))))

(defn parser?
  "true if `x` is an instance of `Parser`, false otherwise."
  [x]
  (instance? Parser x))

(defn make-parser [parse-fn]
  (Parser. parse-fn))

(spec/def ::defparser-args :clojure.core.specs/defn-args)

(spec/fdef paco.core/defparser
  :args ::defparser-args
  :ret var?)

(defmacro defparser
  "Define a function `name` which returns a parser which executes the
  parser returned by `body`. This macro is primarily useful for
  defining recursive parsers. If the parser defined with this macro
  could be constructed purely with function composition, this macro
  should be avoided."
  {:arglists '([name doc-string? attr-map? [params*] & body])}
  [& defparser-args]
  (spec/assert ::defparser-args defparser-args)
  (let [[_ name [_ & fn-specs]] (macroexpand `(defn ~@defparser-args))]
    `(def ~name
       (fn
         ~@(for [[arglist & body] fn-specs
                 :let [x (first body)
                       pre-post-map (when (and (map? x)
                                               (or (contains? x :pre)
                                                   (contains? x :post)))
                                      x)
                       body (if pre-post-map
                              (rest body)
                              body)
                       fn-form (if pre-post-map
                                 `(fn [state#]
                                    ~pre-post-map
                                    ((do ~@body) state#))
                                 `(fn [state#]
                                    ((do ~@body) state#)))]]
             `(~arglist
               (Parser. ~fn-form)))))))

;; ---------------------------------------------------------------------
;; API

(defrecord State [input position]
  IGetInput
  (-get-input [this]
    input)

  IPosition
  (-column [this]
    (-column (-position this)))

  (-line [this]
    (-line (-position this)))

  (-position [this]
    position))

(defn make-state
  ([input]
   {:pre [(clojure/or (string? input)
                      (seq? input))]}
   (let [position (map->Position {:column 1, :line 1})]
     (map->State {:input input, :position position})))
  ([input position]
   {:pre [(clojure/or (string? input)
                      (seq? input))
          (position? position)]}
   (map->State {:input input, :position position})))

(defn parse [parser input]
  (parser (make-state input)))

;; ---------------------------------------------------------------------
;; Parsers

(defparser predicate
  "Given a predicate return a parser which checks `pred` against the
  first value of the state input. If the result is truthy a successful
  state is returned containing the rest of the state input, a new
  position, and the verified value."
  [pred]
  (fn [state]
    (let [input (get-input state)]
      (if (seq input)
        (let [char (first input)
              current-position (position state)]
          (if (pred char)
            (let [new-input (rest input)
                  new-position (next-position current-position char)
                  new-state (make-state new-input new-position)]
              (make-success char new-state))
            (make-failure state (str "unexpected " (pr-str char)))))
        (make-failure state "unexpected end of input")))))

(defparser succeed
  "Return parser which always succeeds with the value `x`. This
  parser consumes no input."
  [x]
  (fn [state]
    (make-success x state)))

(defparser label
  "Wrap `parser` in a new parser which executes `parser` and, if it
  fails, augments it's expected productions to be the singleton set
  including `label`.

  The purpose of this function is primarily to assist in error
  reporting when running a parser fails."
  [parser label]
  (fn [state]
    (let [result (parser state)]
      (if (failure? result)
        (set-labels result #{label})
        result))))

(defparser choice
  "Return a parser which attempts to execute each parser in
  `parsers` returning the first successful state. If none of the
  parsers succeed the last failing state will be returned."
  ([parser]
   {:pre [(or (parser? parser)
              (fn? parser))]}
   (fn [state]
     (parser state)))
  ([parser & more-parsers]
   {:pre [(or (parser? parser)
              (fn? parser))
          (every? (some-fn parser? fn?) more-parsers)]}
   (fn [state]
     (let [result (parser state)]
       (if (success? result)
         result
         (loop [parsers more-parsers
                result result]
           (if (seq parsers)
             (let [parser (first parsers)
                   result* (parser state)]
               (if (success? result*)
                 result*
                 (let [result* (update-labels result* set/union (get-labels result))
                       parsers* (next parsers)]
                   (recur parsers* result*))))
             (update-labels result
              (fn [labels]
                (let [label (str "( "
                                 (string/join " | " labels)
                                 " )")]
                  #{label}))))))))))

(defparser sequence
  "Return a parser which attempts to execute each supplied parser in
  in serial. If all parsers succeed the returned state value will hold
  a vector containing the state value of each returned state. If any
  parser fails the entire parser fails."
  ([parser]
   (fn [state]
     (fmap vector (parser state))))
  ([parser & more-parsers]
   (fn [state]
     (let [result (fmap vector (parser state))]
       (if (success? result)
         (loop [parsers more-parsers
                result result]
           (if (seq parsers)
             (let [parser (first parsers)
                   result* (parser (get-state result))]
               (if (success? result*)
                 (let [result* (fmap
                                (fn [x]
                                  (conj (get-value result) x))
                                result*)
                       parsers* (next parsers)]
                   (recur parsers* result*))
                 result*))
             result))
         result)))))

(defn zero-or-more
  "Helper function utilized by `*` and `+`. Accepts a parser and a
  state and returns a pair of collected values (produced by successful
  executions of `parser`) and a new state with reflecting any consumed
  input."
  {:private true}
  [parser state]
  (let [result (parser state)]
    (if (success? result)
      (let [x (get-value result)
            [xs state*] (zero-or-more parser (get-state result))]
        [(cons x xs) state*])
      [() state])))

(defparser *
  "Return a parser which attempts to execute `parser` zero or more
  times. This parser *always succeeds* and values of successful parser
  are returned in a list."
  [parser]
  (fn [state]
    (let [[xs state*] (zero-or-more parser state)]
      (make-success xs state*))))

(defparser +
  "Return a parser which attempts to execute `parser` one or more
  times."
  [parser]
  (fn [state]
    (let [result (parser state)]
      (if (success? result)
        (let [x (get-value result) 
              [xs state*] (zero-or-more parser (get-state result))]
          (make-success (cons x xs) state*))
        (update-labels result
         (fn [labels]
           (-> (map (fn [label] (str label "+")))
               (transduce conj #{} labels))))))))

(defparser n-times
  "Return a parser which attempts to execute `parser` `n` times."
  [n parser]
  (fn [state]
    (loop [n n
           result (make-success () state)]
      (if (zero? n)
        result
        (let [result* (fmap
                       (fn [x]
                         (cons x (get-value result)))
                       (parser (get-state result)))]
          (if (success? result)
            (let [n* (dec n)]
              (recur n* result*))
            result*))))))

(defparser ?
  "Return a parser which attempts to execute `parser`. If the parser
  succeeds it will return the successful result having consumed
  input. If the parser fails it will also return a successful result,
  however, it will have consumed no input. Thus the returned parser
  *always succeeds*."
  [parser]
  (fn [state]
    (let [result (parser state)]
      (if (success? result)
        result
        (make-success nil state)))))

;; ---------------------------------------------------------------------
;; Macros

(spec/fdef paco.core/with-parse
  :args (spec/cat :bindings :clojure.core.specs/bindings
                  :body (spec/* any?))
  :ret parser?)

(defmacro with-parse
  "Returns a parser which behaves like `clojure.core/let` with the
  exception that binding values are expected to be parsers. Each
  parser is executed in serial and, if successful, binds the
  successful value. Successfully bound values can be used in
  subsequent parser bindings.

  Example:

    (let [parser (with-parse [as (+ (char \\a))
                              bs (+ (char \\b))
                              cs (+ (char \\c))]
                   (str (count as)
                        (count bs)
                        (count cs)))
          result (parse parser \"aaabbcccc\")]
      (get-value result))
    ;; => \"324\"

  In this example we parse a sequence of \\a, \\b, and \\c characters
  returning a concatenated string of their counts.

  Example:

    (let [parser (with-parse [x (choice (char \\a)
                                        (char \\b))
                              y (if (= x \\a)
                                  (char \\d)
                                  (char \\e))]
                   (str x y))
          result (parse parser \"be\")]
      (get-value result))
    ;; => \"be\"

  In this example we parse either the character \\a or \\b and then
  conditionally parse either a \\d or an \\e based on the result value
  of the previous parse. Semantically, this parser matches either the
  sequence \\a then \\d or \\b then \\e.
  "
  [bindings & body]
  (spec/assert :clojure.core.specs/bindings bindings)
  (if (empty? bindings)
    `(succeed nil)
    (let [binding-pairs (reverse (partition 2 bindings))
          ;; Symbols for intermediate states and results which ar
          ;; rebound throughout the macro body for writing convenience.
          state-sym (gensym "state__")
          result-sym (gensym "result__")]
      `(make-parser
        (fn [~state-sym]
          ~(reduce
            (fn [body [binding parser]]
              `(let [~result-sym (~parser ~state-sym)]
                 (if (success? ~result-sym)
                   (let [~binding (get-value ~result-sym)
                         ~state-sym (get-state ~result-sym)]
                     ~body)
                   ~result-sym)))
            (let [[binding parser] (first binding-pairs)]
              `(let [~result-sym (~parser ~state-sym)]
                 (if (success? ~result-sym)
                   (let [~binding (get-value ~result-sym)]
                     (fmap (constantly (do ~@body)) ~result-sym))
                   ~result-sym)))
            (rest binding-pairs)))))))

;; ---------------------------------------------------------------------
;; Single character parsers

(def any-char
  (label
    (predicate
     (fn [x]
       (char? x)))
    "."))

(defparser char
  "Return a parser which matches the character `c`."
  [c]
  {:pre [(char? c)]}
  (label
    (predicate
     (fn [x]
       (= x c)))
    (pr-str c)))

(defparser in-char-range
  "Return a parser which matches any character in the inclusive range
  from `c1` to `c2`."
  [c1 c2]
  {:pre [(<= (long c1) (long c2))]}
  (label
    (predicate
     (fn [x]
       (and (char? x)
            (<= (long c1) (long x) (long c2)))))
    (str \[ (clojure/char c1) \- (clojure/char c2) \])))

(def digit
  "Parser which matches a digit character."
  #?(:clj
     (label
       (predicate
        (fn [x]
          (and (char? x)
               (Character/isDigit ^Character x))))
       "[0-9]")
     :cljs
     (in-char-range \0 \9)))

(def letter
  "Parser which matches a letter. Case insensitive."
  #?(:clj
     (label
       (predicate
        (fn [x]
          (and (char? x)
               (Character/isLetter ^Character x))))
       "[a-zA-Z]")
     :cljs
     (choice (in-char-range \a \z)
             (in-char-range \A \Z))))

(def alphanumeric
  "Parser which matches an alphanumeric character."
  #?(:clj
     (label
       (predicate
        (fn [x]
          (and (char? x)
               (Character/isLetterOrDigit ^Character x))))
       "[a-zA-Z0-9]")
     :cljs
     (choice digit letter)))

(def ascii
  "Parser which matches an ascii character."
  (label
    (predicate
     (fn [x]
       (and (char? x)
            (<= 0 (long x) 127))))
    "[\\x00-\\x7F]"))

(def non-ascii
  "Parser which matches a non-ascii character."
  (label
    (predicate
     (fn [x]
       (and (char? x)
            (<= 128 (long x)))))
    "[^\\x00-\\x7F]"))

(def hex-char
  "Parser which matches a hexadecimal character. Case insensitive."
  (choice (in-char-range \a \f)
          (in-char-range \A \F)
          (in-char-range \0 \9)))

(defn whitespace?
  "true if `x` is a whitespace character, false otherwise."
  {:private true}
  [x]
  (and (char? x)
       (Character/isWhitespace ^Character x)))

(def whitespace
  "Parser which matches a whitespace character."
  (label (predicate whitespace?) "\\s"))

(def not-whitespace
  "Parser which matches a non-whitespace character."
  (label (predicate (complement whitespace?)) "[^\\s]"))

(defn control-character?
  "true if `x` is an ISO control character, false otherwise."
  {:private true}
  [x]
  (and (char? x)
       (Character/isISOControl ^Character x)))

(def control-character
  "Parser which matches an ISO control character."
  (label (predicate control-character?) "[\\x00-\\x20]"))

(def not-control-character
  "Parser which matches a non-ISO control character."
  (label (predicate (complement control-character?)) "[^\\x00-\\x20]"))

;; ---------------------------------------------------------------------
;; Multiple character parsers

(def digits
  "Parser which matches a sequence of digits."
  (fmap (fn [ds]
          (apply str ds))
        (+ digit)))

(def letters
  "Parser which matches a sequence of letters."
  (fmap (fn [ls]
          (apply str ls))
        (+ letter)))

(defparser string
  "Parser which matches the sequence of characters provided by the
  string `s`."
  [s]
  {:pre [(string? s)]}
  (let [string-parser (apply sequence (map char s))]
    (label
      (with-parse [cs string-parser]
        s)  
      (pr-str s))))

(def whitespace*
  "Parser which matches zero or more whitespace characters."
  (fmap (fn [cs]
          (apply str cs))
        (* whitespace)))

(def whitespace+
  "Parser which matches one or more whitespace characters."
  (fmap (fn [cs]
          (apply str cs))
        (+ whitespace)))

(defparser separated-by
  "Return a parser which matches `value-parser` and then a sequence of
  `separator-parser` followed by `value-parser` zero or more
  times. Values produced by `value-parser` are captured in a list."
  [value-parser separator-parser]
  (with-parse [x value-parser
               s? (? separator-parser)
               xs (if s?
                    (separated-by value-parser separator-parser)
                    (succeed ()))]
    (cons x xs)))

(defparser between
  "Return a parser which matches the sequence of `delimiter-parser-1`,
  `content-parser`, and `delimiter-parser-2` capturing the value
  produced by `content-parser`"
  [delimiter-parser-1 delimiter-parser-2 content-parser]
  (with-parse [_ delimiter-parser-1
               x content-parser
               _ delimiter-parser-2]
    x))

(defparser not-followed-by
  "Return a parser which only succeeds if `parser` fails. Consumes no
   input."
  [parser]
  (fn [state]
    (let [result (parser state)]
      (if (success? result)
        (let [x (first (get-input state))]
          (make-failure state (str "unexpected " (pr-str x))))
        (make-success nil state)))))

(defparser prefixed-by
  "Return a parser which executes `prefix-parser` and then
  `suffix-parser` capturing the value by `prefix-parser`."
  [prefix-parser suffix-parser]
  (fn [state]
    (let [prefix-result (prefix-parser state)]
      (if (success? prefix-result)
        (let [suffix-result (suffix-parser (get-state prefix-result))]
          (if (success? suffix-result)
            (make-success (get-value prefix-result) (get-state suffix-result))
            suffix-result))
        prefix-result))))

(defparser suffixed-by
  "Return a parser which executes `prefix-parser` and then
  `suffix-parser` capturing the value by `suffix-parser`."
  [prefix-parser suffix-parser]
  (fn [state]
    (let [prefix-result (prefix-parser state)]
      (if (success? prefix-result)
        (let [suffix-result (suffix-parser (get-state prefix-result))]
          suffix-result)
        prefix-result))))

(defn any-char-but [c & more-cs]
  {:pre [(char? c)
         (every? char? more-cs)]}
  (let [char-set (set (cons c more-cs))]
    (label
      (predicate
       (fn [x]
         (and (char? x)
              (not (contains? char-set x)))))
      (str "[^" (string/join (sort char-set)) "]"))))
