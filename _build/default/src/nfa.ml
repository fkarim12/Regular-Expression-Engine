open List
open Sets

(*********)
(* Types *)
(*********)

type ('q, 's) transition = 'q * 's option * 'q

type ('q, 's) nfa_t = {
  sigma: 's list;
  qs: 'q list;
  q0: 'q;
  fs: 'q list;
  delta: ('q, 's) transition list;
}

(***********)
(* Utility *)
(***********)

(* explode converts a string to a character list *)
let explode (s: string) : char list =
  let rec exp i l =
    if i < 0 then l else exp (i - 1) (s.[i] :: l)
  in
  exp (String.length s - 1) []

(****************)
(* Part 1: NFAs *)
(****************)

let move (nfa: ('q,'s) nfa_t) (qs: 'q list) (s: 's option) : 'q list =
  union (fold_left (fun a curr -> 
    fold_left (fun b delta -> match delta with 
    | (st, None, fin) -> if curr = st && s = None then fin::b else b
    | (st, Some v, fin) -> if curr = st && s = (Some v) then fin::b else b)
    a nfa.delta) [] qs) []

let rec e_closure_helper delta qs = 
  match delta with 
  | [] -> qs
  | (st, state, fin) :: t when (state = None && elem st qs) -> 
    let sub_out = e_closure_helper t qs in 
      if not (elem fin sub_out) then union (union sub_out (e_closure_helper t [fin])) (e_closure_helper t qs)
      else sub_out
  | _ :: t -> e_closure_helper t qs

let e_closure (nfa: ('q,'s) nfa_t) (qs: 'q list) : 'q list =
  e_closure_helper nfa.delta qs

  let rec accept_helper nfa curr final str = 
    match str with 
    | [] -> fold_left (fun acc x -> acc || (subset [x] final)) false (e_closure nfa curr)
    | h::t -> accept_helper nfa (e_closure nfa (move nfa (e_closure nfa curr) (Some h))) final t
  
let accept (nfa: ('q,char) nfa_t) (s: string) : bool =
  accept_helper nfa [nfa.q0] nfa.fs (explode s)

(*******************************)
(* Part 2: Subset Construction *)
(*******************************)

let new_states (nfa: ('q,'s) nfa_t) (qs: 'q list) : 'q list list =
  fold_left (fun acc x -> (e_closure nfa (move nfa qs (Some x)))::acc) [] nfa.sigma

let new_trans (nfa: ('q,'s) nfa_t) (qs: 'q list) : ('q list, 's) transition list =
  fold_left (fun acc x -> (qs, Some x, (e_closure nfa (move nfa qs (Some x))))::acc) [] nfa.sigma

let new_finals (nfa: ('q,'s) nfa_t) (qs: 'q list) : 'q list list =
  fold_left (fun acc x -> if elem x nfa.fs == true then [qs] else acc) [] qs

let rec nfa_to_dfa_step (nfa: ('q,'s) nfa_t) (dfa: ('q list, 's) nfa_t)
    (work: 'q list list) : ('q list, 's) nfa_t =
  let rec nfa_to_dfa_step_aux nfa dfa work restWork = 
    match work with 
    | [] -> dfa
    | h::t -> let temp_dfa = {
      sigma = dfa.sigma;
      qs = remove [] (union dfa.qs (new_states nfa h));
      q0 = dfa.q0;
      fs = union dfa.fs (new_finals nfa h);
      delta = union dfa.delta (new_trans nfa h);
    } in
    if not (subset (new_states nfa (e_closure nfa h)) restWork) 
      then nfa_to_dfa_step_aux nfa temp_dfa 
      (union (new_states nfa (e_closure nfa h)) t)
      (union (new_states nfa (e_closure nfa h)) restWork)
    else nfa_to_dfa_step_aux nfa temp_dfa t restWork 
  in nfa_to_dfa_step_aux nfa dfa work work;; 

let nfa_to_dfa (nfa: ('q,'s) nfa_t) : ('q list, 's) nfa_t =
  let dfa = {
    sigma = nfa.sigma;
    qs = [e_closure nfa [nfa.q0]];
    q0 = [nfa.q0];
    fs = [];
    delta = [];
  } in nfa_to_dfa_step nfa dfa ([e_closure nfa [nfa.q0]])
