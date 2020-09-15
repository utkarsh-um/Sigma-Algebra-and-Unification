exception NOT_UNIFIABLE;;
type variable=string;;

type symbol=string;;

type term = V of variable | Node of symbol * (term list);;

type signature=(symbol*int) list;;

let rec map l f = match l with
	[]->[]
| x::xs -> (f x)::(map xs f);;

let rec foldl f e l = match l with
	[] -> e
| x::xs -> foldl f (f x e) xs;;

let rec filter l p = match l with
	[]->[]
| x::xs -> if (p x) then x::(filter xs p) else (filter xs p);;

(*--------------------------------------------------------------*)

let rec check_sig (sign:signature) =  (* checks whether signature is valid or not *)
	match sign with
	[]->true
| x::xs -> let (s,ar)=x in 
		   let f y e = let (s1,ar1)=y in 
		   			if (String.equal s1 s) then e else (e+1) in
		   let xslen = List.length xs in
		   let xlen = foldl f 0 xs in
		   if (xslen=xlen) && (ar>=0) then check_sig xs
		else false;;

(*--------------------------------------------------------------*)

let rec get_arity (s:symbol) (sign:signature) = match sign with  (*Given a signature and a term returns the arity of the term if present in signature otherwise returns -1*)
	[] -> -1
| x::xs -> let (s1,ar) = x in
			if (String.equal s1 s) then ar else get_arity s xs;;



let rec wfterm (sign:signature) (t:term) = match t with	(* Checks whether term is well-formed or not (i)symbol present in signature (ii)arity and length os terms list is equal (iii)all the terms in term list of this term is well formed *)
	V(x) -> true
| Node(s,tl) -> let ar = (get_arity s sign) in
					if ar = -1 then false
					else if ar = 0 then match tl with
					[] -> true 
					| _ -> false

				else if (ar<>(List.length tl)) then false

			else (check_tl tl sign)
		
and check_tl (tl) (sign) = match  tl with			(* and keyword allows mutual recursive functions,therefore both the fns. can call each other *)
| [] -> true
| x::xs -> if (wfterm sign x) then (check_tl xs sign) else false;;

(*--------------------------------------------------------------*)

let rec ht (sign:signature) (t:term) = match t with 		(* returns the height of the term*)
	V(x) -> 0
| Node(s,tl) -> let ar = (get_arity s sign) in
				if ar=0 then 0
				else let f xt e = let htxt = (ht sign xt ) in if(htxt>e) then htxt else e in
				1 + (foldl f 0 tl);; 

let rec size (sign:signature) (t:term) = match t with 		(* returns the size of the term; total no. of variables and symbols *)
| V(x) -> 1
|  Node(s,tl) -> let ar = (get_arity s sign) in
					if ar=0 then 1
					else let f xt e = let sixt = (size sign xt) in (e+sixt) in
					1 + (foldl f 0 tl);;

let rec addvars l x = match l with 							(* add x to list l if already not present *)
	[]-> x::[]
| f::fs -> if (String.equal f x) then f::fs else f::(addvars fs x);;

let rec vars_help (t:term) (sign:signature) (l:variable list)= match t with (* Given a list l and a term t; add all the variables, which are not present in l but are in t, to l*)
	V(x) -> addvars l x
|  Node(s,tl) -> let ar = (get_arity s sign) in
					if ar=0 then l
				else let f xt e = vars_help xt sign e in
				foldl f l tl;;

let vars (sign:signature) (t:term) = vars_help t sign [];; 	

(*--------------------------------------------------------------*)

type substitution = (variable*term)list;; 			(* substitution is a list of variable*term variable->term *)

let compose (s1:substitution) (s2:substitution) : substitution= s1@s2;; (* composition of substituions s1 s2 is the appended list s1@s2 *)

let rec subst_helper (sign:signature) (sub:(variable*term)) (t:term) = match t with  (*takes a variable*term (v1,t1) and a term t; replace v1 with t1 in t*)
| V(x) -> let (v1,t1) = sub in if (String.equal v1 x) then t1 else t
| Node(s,tl) -> let ar = (get_arity s sign) in
				if ar=0 then t
				else let f xt = subst_helper sign sub xt in
				Node(s,(map tl f));;

let rec subst (sign:signature) (sublis:(substitution)) (t:term) = match sublis with (* takes as substitution(: (term*variable)list) and applies each term*variable to the term one followed by another*)
| [] -> t
| sx::subxs -> subst sign subxs (subst_helper sign sx t);;

(*--------------------------------------------------------------*)

let rec check_vars (l) x = match l with  			(* Given a list l of variables checks whether x is present or not *)
| [] -> false
| f::xs -> if (String.equal f x) then true else  (check_vars xs x);;

let rec mgu (sign:signature) (t1:term) (t2:term) = match (t1,t2) with
| (V(x),V(y)) -> if (String.equal x y) then [] else [(y,V(x))] 			(* V(x),V(y) : y |-> V(x) *)

| (V(x),Node(s,tl)) -> let ar = (get_arity s sign) in 					(* V(x),Node(s,tl) : x |-> Node(s,tl) if x is not present in vars of Node(s,tl) else NOT_UNIFIABLE *)
						if ar=0 then [(x,t2)]
					else let checker = check_vars (vars sign t2) x in
							if checker then raise NOT_UNIFIABLE
						else [(x,t2)]

| (Node(s,tl),V(x)) -> let ar = (get_arity s sign) in 					(* Node(s,tl),V(x) : x |-> Node(s,tl) if x is not present in vars of Node(s,tl) else NOT_UNIFIABLE *)
						if ar=0 then [(x,t1)]
					else let checker = check_vars (vars sign t1) x in
							if checker then raise NOT_UNIFIABLE
						else [(x,t1)]

|(Node(s1,tl1),Node(s2,tl2)) -> if(String.equal s1 s2) then  			(*Node(s1,tl1),Node(s2,tl2) if s1 != s2 NOT_UNIFIABLE else apply the procedure to find mgu *)
								let ar=(get_arity s1 sign) in
									if ar=0 then []
									else  operate_list sign tl1 tl2 []
								else raise NOT_UNIFIABLE

and operate_list (sign:signature) (tlis1: (term list)) (tlis2: (term list)) l = match (tlis1,tlis2) with
| ([],[]) -> l
| (tis1::ts1,tis2::ts2) -> operate_list sign ts1 ts2 (compose l (mgu sign (subst sign l tis1) (subst sign l tis2)));;

(*--------------------------------------------------------------*)

(* In my implementation I have take substitution to be (variable*term) list 

   Composition of substitutions s1 s2 is the list s1 @ s2

   Function subst takes a substitution ((variable*term) list) and then  apply each (variable*term) pair to the input term one followed by another
   i.e. First the head of the list is applied to the input term then the head of remaning list is applied and so on.

   If substitution is [] implies identity function for all variables
 *)