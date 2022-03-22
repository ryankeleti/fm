structure Fm : sig

  (* Evalutes an sexp-formated boolfm with an assignment list.
   * A boolfm has the grammar:
   * p := t
   *    | nil
   *    | x        (any symbol starting with an alpha char)
   *    | (! p)
   *    | (p ^ p)
   *    | (p v p)
   *    | (p => p)
   *    | (p = p)
   *    | (p <> p)
   *    | (p !^ p)
   *    | (p !v p)
   *
   * Note that all symbols ARE case-sensitive, including
   * t and nil (so T is not true, but the var T).
   *)
  val eval : string -> string list -> bool

  (* Runs constant propagation on an sexp-formatted norfm
   * and produces a pretty-printed sexp result or prints
   * an error message.
   *
   * A norfm has the grammar:
   * p := t
   *    | nil
   *    | x        (any symbol starting with an alpha char)
   *    | (p !v p)
   *
   * Note that all symbols ARE case-sensitive, including
   * t and nil (so T is not true, but the var T).
   *)
  val prop : string -> unit

end = struct

(*
 * 1. Subtyping-ish
 *
 * SML does not provide subtype relationships. Hence, I did
 * the next "best" thing, which is to define separate datatypes
 * for each type in the hierarchy and provide explicit translation
 * functions between them.
 *
 * The chain is
 *   nor_ncfm <: nor_cpfm <: norfm <: boolfm1 <: boolfm
 * and given, say, p : norfm, we can call
 *   norfm_as_boolfm p
 * to recover p as a boolfm. Likewise for any pair.
 *
 * This is slightly awkward/contrived for this situation, but I
 * think it captures the general ML approach to datatype
 * relationships, such as transformations between IRs.
 *)

(* BoolFm *)
datatype boolfm =
    Bool of bool
  | Var of string
  | Not of boolfm
  | And of boolfm * boolfm
  | Or of boolfm * boolfm
  | Impl of boolfm * boolfm
  | Eq of boolfm * boolfm
  | Xor of boolfm * boolfm
  | Nor of boolfm * boolfm
  | Nand of boolfm * boolfm

(* BoolFm1 *)
datatype boolfm1 =
    Bool_1 of bool
  | Var_1 of string
  | Not_1 of boolfm1
  | And_1 of boolfm1 * boolfm1
  | Or_1 of boolfm1 * boolfm1
  | Impl_1 of boolfm1 * boolfm1
  | Eq_1 of boolfm1 * boolfm1
  | Xor_1 of boolfm1 * boolfm1
  | Nor_1 of boolfm1 * boolfm1

(* NorFm *)
datatype norfm =
    N_bool of bool
  | N_var of string
  | N_nor of norfm * norfm

(* NorNCFm *)
datatype nor_ncfm =
    Nc_var of string
  | Nc_nor of nor_ncfm * nor_ncfm

(* NorCPFm *)
datatype nor_cpfm =
    Ncp_bool of bool
  | Ncp_ncfm of nor_ncfm

(*
 * CONVERSION FUNCTIONS
 *)

(* boolfm1 <: boolfm *)
fun boolfm1_as_boolfm (Bool_1 b) = Bool b
  | boolfm1_as_boolfm (Var_1 v) = Var v
  | boolfm1_as_boolfm (Not_1 f) = Not (boolfm1_as_boolfm f)
  | boolfm1_as_boolfm (And_1 (p, q)) = And (boolfm1_as_boolfm p, boolfm1_as_boolfm q)
  | boolfm1_as_boolfm (Or_1 (p, q)) = Or (boolfm1_as_boolfm p, boolfm1_as_boolfm q)
  | boolfm1_as_boolfm (Impl_1 (p, q)) = Impl (boolfm1_as_boolfm p, boolfm1_as_boolfm q)
  | boolfm1_as_boolfm (Eq_1 (p, q)) = Eq (boolfm1_as_boolfm p, boolfm1_as_boolfm q)
  | boolfm1_as_boolfm (Xor_1 (p, q)) = Xor (boolfm1_as_boolfm p, boolfm1_as_boolfm q)
  | boolfm1_as_boolfm (Nor_1 (p, q)) = Nor (boolfm1_as_boolfm p, boolfm1_as_boolfm q)

(* norfm <: boolfm1 *)
fun norfm_as_boolfm1 (N_bool b) = Bool_1 b
  | norfm_as_boolfm1 (N_var v) = Var_1 v
  | norfm_as_boolfm1 (N_nor (p, q)) = Nor_1 (norfm_as_boolfm1 p, norfm_as_boolfm1 q)

(* norfm <: boolfm *)
fun norfm_as_boolfm p = boolfm1_as_boolfm (norfm_as_boolfm1 p)

(* nor_ncfm <: norfm *)
fun nor_ncfm_as_norfm (Nc_var v) = N_var v
  | nor_ncfm_as_norfm (Nc_nor (p, q)) = N_nor (nor_ncfm_as_norfm p, nor_ncfm_as_norfm q)

(* nor_cpfm <: norfm *)
fun nor_cpfm_as_norfm (Ncp_bool b) = N_bool b
  | nor_cpfm_as_norfm (Ncp_ncfm f) = nor_ncfm_as_norfm f

(* nor_cpfm <: boolfm1 *)
fun nor_cpfm_as_boolfm1 p = norfm_as_boolfm1 (nor_cpfm_as_norfm p)

(* nor_cpfm <: boolfm *)
fun nor_cpfm_as_boolfm p = boolfm1_as_boolfm (nor_cpfm_as_boolfm1 p)

(* nor_ncfm <: nor_cpfm *)
fun nor_ncfm_as_nor_cpfm p = Ncp_ncfm p

(* nor_ncfm <: norfm *)
fun nor_ncfm_as_norfm p = nor_cpfm_as_norfm (nor_ncfm_as_nor_cpfm p)

(* nor_ncfm <: boolfm1 *)
fun nor_ncfm_as_boolfm1 p = norfm_as_boolfm1 (nor_ncfm_as_norfm p)

(* nor_ncfm <: boolfm *)
fun nor_ncfm_as_boolfm p = boolfm1_as_boolfm (nor_ncfm_as_boolfm1 p)

(*** Boolean Operators ***)
structure B = struct
  (* => boolean op *)
  fun impl x y = (not x) orelse y

  (* <=> boolean op *)
  fun iff (x : bool) (y : bool) = x = y

  (* xor boolean op *)
  fun xor x y = (x orelse y) andalso not (x andalso y)

  (* nor boolean op *)
  fun nor x y = not (x orelse y)

  (* nand boolean op *)
  fun nand x y = not (x andalso y)
end

(*
 * 2. Semantics/evaluation
 * 
 * The semantics of boolfm + family is the same as HWK5.
 * The glaring difference is that Eval.bf_eval cannot be
 * called on any "subtype" directly, but must instead be
 * converted into a boolfm using a conversion function
 * beforhand.
 *)
structure Eval = struct
  (* list of vars *)
  type assignment = string list

  (* var lookup *)
  fun lookup (v : string) (a : assignment) =
    List.exists (fn x => x = v) a

  (* boolfm evaluator *)
  fun bf_eval (Bool b) _ = b
    | bf_eval (Var v) a = lookup v a
    | bf_eval (Not p) a = not (bf_eval p a)
    | bf_eval (And (p, q)) a = (bf_eval p a) andalso (bf_eval q a)
    | bf_eval (Or (p, q)) a = (bf_eval p a) orelse (bf_eval q a)
    | bf_eval (Impl (p, q)) a = B.impl (bf_eval p a) (bf_eval q a)
    | bf_eval (Eq (p, q)) a = B.iff (bf_eval p a) (bf_eval q a)
    | bf_eval (Xor (p, q)) a = B.xor (bf_eval p a) (bf_eval q a)
    | bf_eval (Nor (p, q)) a = B.nor (bf_eval p a) (bf_eval q a)
    | bf_eval (Nand (p, q)) a = B.nand (bf_eval p a) (bf_eval q a)
end

(* Helper for const_prop_norfm
 * unwraps a nor_ncfm inside a nor_cpfm *)
fun unwrap (Ncp_ncfm p) = p
  | unwrap _ = raise Fail "unreachable" 

(* Helper for const_prop_norfm
 * converts norfm -> nor_cpfm *)
fun cast (N_bool b) = Ncp_bool b
  | cast (N_var v) = Ncp_ncfm (Nc_var v)
  | cast (N_nor (p, q)) = Ncp_ncfm (Nc_nor (unwrap (cast p), unwrap (cast q)))

(*
 * 3. Constant propagation
 *
 * Here we define the constant propagation formula. The structure is almost
 * identical to the HWK5 solution, except we have to play around a bit with
 * "subtypes" (namely norfm -> nor_cpfm and nor_cpfm -> nor_ncfm where
 * applicable).
 *)
fun const_prop_norfm p = 
  case p of
    N_nor (q, r) =>
      let
        val nq = const_prop_norfm q
        val nr = const_prop_norfm r
      in
        case (nq, nr)
          of (Ncp_bool true, _) => Ncp_bool false
           | (_, Ncp_bool true) => Ncp_bool false
           | (Ncp_bool false, Ncp_bool false) => Ncp_bool true
           | (Ncp_bool false, _) => Ncp_ncfm (Nc_nor (unwrap nr, unwrap nr))
           | (_, Ncp_bool false) => Ncp_ncfm (Nc_nor (unwrap nq, unwrap nq))
           | (_, _) => Ncp_ncfm (Nc_nor (unwrap nq, unwrap nr))
      end
    | _ => cast p;

(*
 * The rest of this file is dedicated to an interface to the code
 * using the "eval" and "prop" functions. These function will accept a string
 * formatted like a BoolFm or a NorFm sexp (sans quoting) respectively in
 * ACL2s and run constant evaluation / propagation on them.
 *
 * The result will be a boolean / an sexp printed to stdout or a parse error.
 * The input grammars are described at the top of the file.
 *
 * Intentionally, only the eval and prop function are exposed in the Fm module,
 * and hence the only entrypoint for running the code. The parser provides
 * that interface.
 *
 * That means you can't access the types without changing the code. But exposing
 * them is trivial. I just wanted to highlight the evaluation and constant
 * propagation. If you want, you can remove the restrictive signature and access
 * all the gory internals for yourself.
 *)

(*** Parser for boolfm and norfm ***)
structure Parser : sig
  exception ParseError of string

  (* Parses an sexp string into a boolfm following grammar defined in Fm.eval,
   * throws ParseError on failure *)
  val parse_boolfm : string -> boolfm

  (* Parses an sexp string into a norfm following grammar defined in Fm.prop,
   * throws ParseError on failure *)
  val parse_norfm : string -> norfm
end = struct
  structure S = SExp
  exception ParseError of string

  (* Parse a string to an sexp *)
  fun to_sexp s =
    SExpParser.parse (TextIO.openString s)

  (* Ensures input sexp is of the proper form,
   * and converts all symbols to uppercase strings *)
  fun sanitize sexp =
    let
      fun unwrap [S.LIST l] = S.LIST l
        | unwrap [S.SYMBOL a] = S.SYMBOL a
        | unwrap _ = raise ParseError "invalid expression"

      fun wf [] = true
        | wf ((S.SYMBOL _)::s) = wf s
        | wf ((S.LIST l)::s) = (wf l) andalso (wf s)
        | wf _ = false

      fun stringify (S.SYMBOL a) = S.STRING (Atom.toString a)
        | stringify (S.LIST l) = S.LIST (List.map stringify l)
        | stringify s = s
    in
      if wf sexp
      then stringify (unwrap sexp)
      else raise ParseError "not well-formed"
    end

  (* Sexp to boolfm parsing *)
  fun parse_sexp (S.STRING "t") = Bool true
    | parse_sexp (S.STRING "nil") = Bool false
    | parse_sexp (S.STRING v) = if Char.isAlpha (String.sub (v, 0))
                                then Var v
                                else raise ParseError ("invalid variable " ^ v)
    | parse_sexp (S.LIST [S.STRING "!", p]) = Not (parse_sexp p)
    | parse_sexp (S.LIST [p, S.STRING "^", q]) = And (parse_sexp p, parse_sexp q)
    | parse_sexp (S.LIST [p, S.STRING "v", q]) = Or (parse_sexp p, parse_sexp q)
    | parse_sexp (S.LIST [p, S.STRING "=>", q]) = Impl (parse_sexp p, parse_sexp q)
    | parse_sexp (S.LIST [p, S.STRING "=", q]) = Eq (parse_sexp p, parse_sexp q)
    | parse_sexp (S.LIST [p, S.STRING "<>", q]) = Xor (parse_sexp p, parse_sexp q)
    | parse_sexp (S.LIST [p, S.STRING "!v", q]) = Nor (parse_sexp p, parse_sexp q)
    | parse_sexp (S.LIST [p, S.STRING "!^", q]) = Nand (parse_sexp p, parse_sexp q)
    | parse_sexp _ = raise ParseError "invalid expression"

  fun boolfm_to_norfm (Bool b) = N_bool b
    | boolfm_to_norfm (Var v) = N_var v
    | boolfm_to_norfm (Nor (p, q)) = N_nor (boolfm_to_norfm p, boolfm_to_norfm q)
    | boolfm_to_norfm _ = raise ParseError "invalid expression"

  (* Parses a string into a boolfm given spec in Fm.eval *)
  fun parse_boolfm s =
    parse_sexp (sanitize (to_sexp s))

  (* Parses a string into a norfm given spec in Fm.prop *)
  fun parse_norfm s =
    boolfm_to_norfm (parse_boolfm s)
end

(*** Pretty printing ***)
structure PP : sig
  (* Pretty print a constant-propagated formula *)
  val pp_cp : nor_cpfm -> int -> unit
end = struct
  structure S = SExp
  structure SPP = SExpPP

  fun as_sexp (Ncp_bool true) = S.SYMBOL (Atom.atom "t")
    | as_sexp (Ncp_bool false) = S.SYMBOL (Atom.atom "nil")
    | as_sexp (Ncp_ncfm p) = as_sexp_nc p
  and as_sexp_nc (Nc_var v) = S.SYMBOL (Atom.atom v)
    | as_sexp_nc (Nc_nor (q, r)) = S.LIST [as_sexp_nc q, S.SYMBOL (Atom.atom "v"), as_sexp_nc r]

  fun pp_cp p w =
    let
      val pps = TextIOPP.openOut { dst=TextIO.stdOut, wid=w }
    in
      SPP.output (pps, as_sexp p);
      TextIOPP.closeStream pps
    end
end

(* Convenience function to run evaluation on an sexp boolfm
 * and assignment *)
fun eval s a =
  (Eval.bf_eval (Parser.parse_boolfm s) a)
    handle (Parser.ParseError s) => (print (s ^ "\n"); false)

(* Convenience function to run constant propagation on an
 * sexp norfm and produce a pretty-printed sexp result *)
fun prop s =
  (PP.pp_cp (const_prop_norfm (Parser.parse_norfm s)) 80)
    handle (Parser.ParseError s) => print (s ^ "\n")

end

(*
 * 4. Interesting things?
 *
 * It was interesting to attempt to mimic subtyping in SML. There might be
 * a more clever way of doing things, but this seems like the most idiomatic
 * approach. Implementing a little sexp interface was a fun exercise too. 
 *)

