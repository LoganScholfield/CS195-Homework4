(*
   Homework 4, Problem 7: Completing the CatML interpreter.
   In this OCaml code file you will find the beginning of various functions with
   COMPLETE ME tags in the comments, that you must complete to obtain a *correct*
   interpreter for the CatML language. This includes: subst, closed, and redx.
   Both the tracer and stepper functions (with pretty printing) have been completed
   for you and can be used for testing examples as you work on the assignment. Example
   expressions for testing can be found in the course github repository.
   You should submit this file once completed. Your submission must be executable
   OCaml code.
*)

(*
   Abstract Syntax
   ---------------
  
   The expr datatype defines the ASTs for CatML. The mapping from CatML concrete syntax
   to abstract syntax is as follows, in full detail.
 
   [[True]] = Bool(true)
   [[False]] = Bool(false)
   [[n]] = Nat(n)           for any natural number n
   [[x]] = Var(Ident("x"))       for any variable x
   [[e1 + e2]] = Plus([[e1]], [[e2]])
   [[e1 - e2]] = Minus([[e1]], [[e2]])
   [[e1 And e2]] = And([[e1]], [[e2]])
   [[e1 Or e2]] = Or([[e1]], [[e2]])
   [[Not e]] = Not([[e]])
   [[(e1, e2)]] = Pair([[e1]], [[e2]])
   [[Fst(e)]] = Fst([[e]])
   [[Snd(e)]] = Snd([[e]])
   [[e1 e2]] = Appl([[e1]], [[e2]])
   [[Let x = e1 in e2]] = Let(Ident("x"), [[e1]], [[e2]])
   [[(Fun x . e)]] = Fun(Ident("x"), [[e]])
   [[(Fix z . x . e)]] = Fix(Ident("z"), Ident("x"), [[e]])
*)

type ident = Ident of string

type expr =
(* boolean expression forms *)
    Bool of bool | And of expr * expr | Or of expr * expr | Not of expr
(* arithmetic expression forms *)
  | Nat of int | Plus of expr * expr | Minus of expr * expr | Equal of expr * expr
(* functional expression forms *)
  | Function of ident * expr | Appl of expr * expr | Var of ident
(* pairs *)
  | Pair of expr * expr | Fst of expr | Snd of expr
(* other forms *)
  | If of expr * expr * expr | Let of ident * expr * expr | Fix of ident * ident * expr

exception AssignmentIncomplete

(*
   Closed expression check
   ------------------------
   Since reduction is defined only on closed expressions, we need to implement
   a check to ensure that an input expression is closed. Since closure is preserved
   by reduction, this check can be performed once statically on source code,
   as in tracer and stepper below.									     
   closed : Dast.expr -> Dast.ident list -> bool
   in : an expression e and an identifier list ilist
   out : true iff e is closed, assuming every element of ilist is 
         a bound variable
*)
let rec closed e ident_list =
  match e with
    Nat(_) -> true
  | Bool(_) -> true
  | Var(x) -> List.mem x ident_list
  | And(e1,e2) -> (closed e1 ident_list) && (closed e2 ident_list)
  | Plus(e1, e2) -> (closed e1 ident_list) && (closed e2 ident_list)
  | Let(x,e1,e2) -> (closed e1 ident_list) && (closed e2 (x::ident_list))
  | _ -> raise AssignmentIncomplete;;

(*
   Substitution
   ------------
   We implement substitution as defined symbolically, to obtain a substution-based
   semantics in the interpreter.
  
   subst : Dast.expr -> Dast.expr -> Dast.ident -> Dast.expr
   in : expression e1, expression e2, identifier id
   out : e1[e2/id] 
*)


let rec subst e1 e2 id =
  match e1 with
    Bool(b) -> Bool(b)
  | Nat(b) -> Nat(b)
  | Not(b) -> Not(subst b e2 id)
  | Pair(ea,eb) -> Pair(subst ea e2 id, subst eb e2 id)
  | Fst(e) -> Fst(subst e e2 id)
  | Snd(e) -> Snd(subst e e2 id)
  | Appl(ea,eb) -> Appl(subst ea e2 id, subst eb e2 id)
  | Var(x) -> if x = id then e2 else (Var x)
  | And(ea,eb) -> And(subst ea e2 id, subst eb e2 id)
  | Or(ea,eb) -> Or(subst ea e2 id, subst eb e2 id)
  | Plus(ea,eb) -> Plus(subst ea e2 id, subst eb e2 id)
  | Minus(ea,eb) -> Minus(subst ea e2 id, subst eb e2 id)
  | Let(x,ea,eb) ->
      if x = id then Let(x, subst ea e2 id, eb)
      else Let(x, subst ea e2 id, subst eb e2 id)
  |Function(x,ea) -> if x = id then Function(x,ea) else Function(x, subst ea e2 id)
  |Fix(z,y,e) -> if id = z || id = y then Fix(z,y,e) else Fix(z, y, subst e e2 id)
  | _ -> raise AssignmentIncomplete;;

   (*[[(Fun x . e)]] = Fun(Ident("x"), [[e]])*)

(*
   Value predicate
   ---------------
   Checking whether a given expression is a value is critical for the operational 
   semantics. 
   isval : expr -> bool
   in : expression e
   out : true iff e is a value
*)
let rec isval = function
    Nat(_) -> true
  | Bool(_) -> true
  | Function(_) -> true
  | Fix(_) -> true
  | Pair(e1, e2) -> isval e1 && isval e2
  | _ -> false

exception NotReducible
(*
   Single step reduction
   ---------------------
   Single (aka small) step reduction is the heart of the operational semantics. Pattern
   matching allows a tight connection with the symbolic definition of the semantics.
   
   redx : expr -> expr
   in : AST [[e]]
   out : AST [[e']] such that e -> e' in the operational semantics
   side effect : exception NotReducible raised if [[e]] isn't reducible in implementation.
*)
let rec redx e = match e with
    Not(Bool(false)) -> Bool(true)
  | Not(Bool(true)) -> Bool(false)
  | And(Bool(_), Bool(false)) -> Bool(false)
  | And(Bool(true), Bool(true)) -> Bool(true)
  | And(Bool(false), Bool(_)) -> Bool(false)
  | Or(Bool(true), Bool(_)) -> Bool(true)
  | Or(Bool(false), Bool(false)) -> Bool(false)
  | Or(Bool(false), Bool(true)) -> Bool(true)
  | Not(e) -> Not(redx e)
  | And(e1,e2) -> if isval e1 then And(e1, redx e2) else And(redx e1, e2)
  | Or(e1, e2) -> if isval e1 then Or(e1, redx e2) else Or(redx e1, e2)
  | Let(x,e1,e2) -> if isval e1 then (subst e2 e1 x) else Let(x,redx e1,e2)
  | Plus(Nat(a), Nat(b)) -> Nat(a+b)
  | Plus(e1,e2) -> if isval e1 then Plus(e1, redx(e2)) else Plus (redx e1,e2)
  | Minus(Nat(a), Nat(b)) -> Nat(if a > b then a-b else 0)
  | Minus(e1,e2) -> if isval e1 then Minus(e1, redx(e2)) else Minus (redx e1,e2)
  | Equal(Nat(a), Nat(b)) -> Bool(a=b)
  | Equal(e1,e2) -> if isval e1 then Equal(e1, redx(e2)) else Equal (redx e1,e2) 
  | Appl(e1,e2) -> Appl(redx e1,e2)
  | Pair(e1,e2) -> Pair(redx e1, redx e2)
  | Fst(e1) -> if isval e1 then e1 else redx e1
  | Snd(e2) -> if isval e2 then e2 else redx e2
  | Function(x,e) -> raise AssignmentIncomplete
  | Fix(z,y,e) -> raise AssignmentIncomplete
  | _ -> raise AssignmentIncomplete;;


(* 
   [[(Fix z . x . e)]] = Fix(Ident("z"), Ident("x"), [[e]])*)

exception StuckExpression;;
(*
   Multistep reduction
   -------------------
   redxs : expr -> expr
   in : AST [[e]]
   out : [[v]] such that e ->* v in the operational semantics
*)
let rec redxs e = if isval e then e else redxs (try (redx e) with NotReducible -> raise StuckExpression)


open Printf;;

(*
  prettyPrint : expr -> string
  in : An expression AST [[e]].
  out : The concrete expression e in string format.
*)
let rec prettyPrint e = match e with
  | Bool true -> "True"
  | Bool false -> "False"
  | Nat n -> sprintf "%i" n
  | Var(Ident(x)) -> x
  | And (e1, e2) -> "(" ^ (prettyPrint e1) ^ " And " ^ (prettyPrint e2) ^ ")"
  | Or (e1, e2) -> "(" ^ (prettyPrint e1) ^ " Or " ^ (prettyPrint e2) ^ ")"
  | Not e1 -> "(Not " ^ (prettyPrint e1) ^ ")"
  | Plus (e1, e2) -> "(" ^ (prettyPrint e1) ^ " + " ^ (prettyPrint e2) ^ ")"
  | Minus (e1, e2) -> "(" ^ (prettyPrint e1) ^ " - " ^ (prettyPrint e2) ^ ")"
  | Equal (e1, e2) -> "(" ^ (prettyPrint e1) ^ " = " ^ (prettyPrint e2) ^ ")"
  | If(e1, e2, e3) -> "If " ^ (prettyPrint e1) ^
                      " Then " ^ (prettyPrint e2) ^
                      " Else " ^ (prettyPrint e3)
  | Function(Ident(x), e) -> "(Fun " ^ x ^ " . " ^ (prettyPrint e) ^ ")"
  | Fix(Ident(z), Ident(x), e) -> "(Fix " ^ z ^ " . " ^ x ^ " . " ^ (prettyPrint e) ^ ")"
  | Let(Ident(x), e1, e2) -> "Let " ^ x ^ " = " ^ (prettyPrint e1) ^ " In\n" ^ (prettyPrint e2)
  | Appl(e1, e2) -> (prettyPrint e1) ^ " " ^ (prettyPrint e2)
  | Pair(e1, e2) -> "(" ^ (prettyPrint e1) ^ ", " ^ (prettyPrint e2) ^ ")"
  | Fst(e1) ->
      (match e1 with Pair(_) -> "Fst" ^  (prettyPrint e1)
                   | _ ->  "Fst(" ^  (prettyPrint e1) ^ ")")
  | Snd(e1) ->
      (match e1 with Pair(_) -> "Snd" ^  (prettyPrint e1)
                   | _ ->  "Snd(" ^  (prettyPrint e1) ^ ")")


exception NotClosed;;

(*
  pretty_trace : expr -> bool -> unit
  in : AST [[e]]
  out : () 
  side effects : prints intermediate expressions (aka the reduction trace) 
    during evaluation; if stepper flag is on, blocks on keystroke between 
    reductions.  
*)
let rec pretty_trace e stepper =
  (printf "%s" (prettyPrint e); if stepper then ignore (read_line()) else ();
   if (isval e) then (printf "\n"; flush stdout) else
     try
       (
         let e' = redx e in
         (printf "->\n"; flush stdout; pretty_trace e' stepper)
       )
     with NotReducible ->  (printf "  (Bad, Stuck Expression)\n"; flush stdout))

(*
  stepper : expr -> expr
  in : AST [[e]]
  out : [[v]] such that e ->* v in the operational semantics
  side effects : Blocks on keystroke between reductions, prints intermediate 
    expressions (aka the reduction trace) during evaluation; 
    raises NotClosed if e is not closed.     
*)
let rec stepper e = if (closed e []) then (pretty_trace e true) else raise NotClosed ;;
(*
  tracer : expr -> expr
  in : AST [[e]]
  out : [[v]] such that e ->* v in the operational semantics
  side effects : prints intermediate expressions (aka the reduction trace) during evaluation; 
    raises NotClosed if e is not closed. 
*)
let rec tracer e =  if (closed e []) then (pretty_trace e false) else raise NotClosed;;
