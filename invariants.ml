open Printf

(* Définitions de terme, test et programme *)
type term = 
  | Const of int
  | Var of int
  | Add of term * term
  | Mult of term * term

type test = 
  | Equals of term * term
  | LessThan of term * term

let tt = Equals (Const 0, Const 0)
let ff = LessThan (Const 0, Const 0)
 
type program = {nvars : int; 
                inits : term list; 
                mods : term list; 
                loopcond : test; 
                assertion : test}

let x n = "x" ^ string_of_int n

(* Question 1. Écrire des fonctions `str_of_term` et `str_of_term` qui
   convertissent des termes et des tests en chaînes de caractères du
   format SMTLIB.

  Par exemple, str_of_term (Var 3) retourne "x3", str_of_term (Add
   (Var 1, Const 3)) retourne "(+ x1 3)" et str_of_test (Equals (Var
   2, Const 2)) retourne "(= x2 2)".  *)
let rec str_of_term t = match t with 
  | Const(y) -> string_of_int y
  | Var(y) -> x y
  | Add(y, z) -> "(+ "^(str_of_term y)^ " "^(str_of_term z)^")"
  | Mult(y, z) -> "(* "^(str_of_term y)^" "^(str_of_term z)^")"

let str_of_test t = match t with 
  | Equals(y, z) -> "(= "^(str_of_term y)^" "^(str_of_term z)^")"
  | LessThan(y, z) -> "(< "^(str_of_term y)^" "^(str_of_term z)^")"

let string_repeat s n =
  Array.fold_left (^) "" (Array.make n s)

(* Question 2. Écrire une fonction str_condition qui prend une liste
   de termes t1, ..., tk et retourne une chaîne de caractères qui
   exprime que le tuple (t1, ..., tk) est dans l'invariant.  Par
   exemple, str_condition [Var 1; Const 10] retourne "(Invar x1 10)".
*)

let str_condition l =
  let rec loop l accu = match l with
    | [] -> accu ^ ")"
    | hd :: tl -> loop tl (accu ^ " "^str_of_term hd)
  in loop l "(Invar"


(* Question 3. Écrire une fonction str_assert_for_all qui prend en
   argument un entier n et une chaîne de caractères s, et retourne
   l'expression SMTLIB qui correspond à la formule "forall x1 ... xk
   (s)".
*)
let str_assert s = "(assert " ^ s ^ ")"

let str_assert_forall n s =
  let tmp = n in    
  let make_x n = 
    let rec loop accu num = match num with
      | 0 -> accu
      | num -> 
          if num = tmp then 
            loop ( "("^ (x num) ^ " Int)" ^ accu) (num-1)
          else loop ( "("^ (x num) ^ " Int) " ^ accu) (num-1)
    in loop "" n 
  in
  str_assert ( "(forall (" ^ make_x n ^")" ^ " (" ^ s ^ "))" )

(* Question 4. Nous donnons ci-dessous une définition possible de la
   fonction smt_lib_of_wa. Complétez-la en écrivant les définitions de
   loop_condition et assertion_condition. *)
      
let smtlib_of_wa p =

  let check_condition t = match t with
  | Equals(y, z)-> (y, z)
  | LessThan(y, z) -> (y, z) in

  let get_terms n =
    let rec loop accu num = match num with 
    | 0 -> accu 
    | _ -> loop ( (Var num) :: accu ) ( num-1 )
  in loop [] n in

  let declare_invariant n =
    "; synthèse d'invariant de programme\n"
    ^"; on déclare le symbole non interprété de relation Invar\n"
    ^"(declare-fun Invar (" ^ string_repeat "Int " n ^  ") Bool)" in

  let loop_condition p =
    let transform_mods (list: term list): string = 
      let rec loop l accu = match l with 
        | [] -> accu
        | hd :: tl -> loop tl (accu ^ str_of_term hd)
      in loop list ""
    in
    str_assert_forall p.nvars ("=> (and "
                              ^str_condition (get_terms p.nvars)
                               ^" "
                               ^""^
                               str_of_test(p.loopcond)
                               ^") (Invar "^transform_mods p.mods
                               ^ ")") in 
  let initial_condition p =
    "; la relation Invar est vraie initialement\n"
    ^str_assert (str_condition p.inits) in

  let assertion_condition p =
    let cnd = check_condition p.loopcond in 
    "; l'assertion finale est vérifiée\n"
    ^str_assert_forall p.nvars ("=> (and "
                                ^str_condition (get_terms p.nvars)
                                ^" "
                                ^"(>= "^
                                str_of_term(fst(cnd))
                                ^" "^str_of_term(snd(cnd))^")"
                                ^""
                                ^ ") "^str_of_test(p.assertion)) in
  let call_solver =
    "; appel au solveur\n(check-sat-using (then qe smt))\n(get-model)\n(exit)\n" in

  String.concat "\n" [declare_invariant p.nvars;
                      loop_condition p;
                      initial_condition p;
                      assertion_condition p;
                      call_solver]

let p1 = {nvars =2; inits =[Const (0); Const(0)];
          mods = [Add(Var(1), Const(1)); Add(Var(2), Const(3))];
          loopcond = LessThan(Var(1), Const(3));
          assertion = Equals(Var(2), Const(9))}
        
(* Question 5. Vérifiez que votre implémentation donne un fichier
   SMTLIB qui est équivalent au fichier que vous avez écrit à la main
   dans l'exercice 1. Ajoutez dans la variable p2 ci-dessous au moins
   un autre programme test, et vérifiez qu'il donne un fichier SMTLIB
   de la forme attendue. *)

let p2 = {nvars = 2;
          inits = [(Const 0) ; (Const 1)];
          mods = [Add ((Var 1), (Const 2)); Add ((Var 2), (Const 1))];
          loopcond = LessThan ((Var 1),(Const 10));
          assertion = Equals ((Var 2),(Const 9))}

let () = Printf.printf "%s" (smtlib_of_wa p1)

