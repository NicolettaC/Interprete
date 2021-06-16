type ide = string;;


type typename = BooleanType | IntegerType | StringType

type exp = Eint of int | Ebool of bool | Estring of string | Set of exp 
         | Den of ide | Singletone of exp | Emptyset of exp | Etypename of typename 
         | Prod of exp * exp | Sum of exp * exp | Diff of exp * exp | Eq of exp * exp | Minus of exp | IsZero of exp 
         | Ifthenelse of exp * exp * exp | Let of ide * exp * exp | Fun of ide * exp | FunCall of exp * exp | Letrec of ide * exp * exp
         | And of exp * exp | Or of exp * exp | Not of exp
         | Union of exp * exp | Intersection of exp * exp | Difference of exp * exp
         | Insert of exp * exp | Remove of exp * exp 
         | CheckEmpty of exp | Contains of exp * exp | CheckSubset of exp * exp
         | MinSet of exp | MaxSet of exp 
         | ForAll of exp * exp | Exists of exp*exp | Map of exp*exp | Filter of exp * exp
;;

(*ambiente*)
type 't env = ide -> 't;;
let emptyenv (v : 't) = function x -> v;;
let applyenv (r : 't env) (i : ide) = r i;;
let bind (r : 't env) (i : ide) (v : 't) = function x -> if x = i then v else applyenv r x;;

(*tipi esprimibili*)
type setT = Empty of typename | Set of evT list * typename
and evT = Int of int | Bool of bool | String of string | Unbound | FunVal of evFun | RecFunVal of ide * evFun | SetVal of setT
and evFun = ide * exp * evT env
              
(*rts*)

(*Controllo dei tipi sugli argomenti delle funzioni di set*) 
(*Restituisce tipo di V*)

let typeof (v: evT) : typename = match v with
    Int(_) -> IntegerType |
    Bool(_) -> BooleanType |
    String(_) -> StringType | 
    _ -> failwith("not an expressable value")

(*type checking*)
let typecheck (s : string) (v : evT) : bool = match s with
    "int" -> (match v with
        Int(_) -> true |
        _ -> false) |
    "bool" -> (match v with
        Bool(_) -> true |
        _ -> false) |
    "string" -> (match v with
        String(_) -> true |
        _ -> false) |
    "set" -> (match v with
        (SetVal(_)) -> true |
        _ -> false) |
    _ -> failwith("not a valid type");; 

(*funzioni primitive*)
let prod x y = if (typecheck "int" x) && (typecheck "int" y)
  then (match (x,y) with
        (Int(n),Int(u)) -> Int(n*u))
  else failwith("Type error");;

let sum x y = if (typecheck "int" x) && (typecheck "int" y)
  then (match (x,y) with
        (Int(n),Int(u)) -> Int(n+u))
  else failwith("Type error");;

let diff x y = if (typecheck "int" x) && (typecheck "int" y)
  then (match (x,y) with
        (Int(n),Int(u)) -> Int(n-u))
  else failwith("Type error");;

let eq x y = if (typecheck "int" x) && (typecheck "int" y)
  then (match (x,y) with
        (Int(n),Int(u)) -> Bool(n=u))
  else failwith("Type error");;


let minus x = if (typecheck "int" x) 
  then (match x with
        Int(n) -> Int(-n))
  else failwith("Type error");;

let iszero x = if (typecheck "int" x)
  then (match x with
        Int(n) -> Bool(n=0))
  else failwith("Type error");;


let vel x y = if (typecheck "bool" x) && (typecheck "bool" y)
  then (match (x,y) with
        (Bool(b),Bool(e)) -> (Bool(b||e)))
  else failwith("Type error");;

let et x y = if (typecheck "bool" x) && (typecheck "bool" y)
  then (match (x,y) with
        (Bool(b),Bool(e)) -> Bool(b&&e))
  else failwith("Type error");;

let non x = if (typecheck "bool" x)
  then (match x with
        Bool(true) -> Bool(false) |
        Bool(false) -> Bool(true))
  else failwith("Type error") ;;

let rec containlst ls x=
  match ls with 
  | [] -> false            
  | h :: t -> if h=x then true 
      else containlst t x ;; 

(* Restituisce le etichette del tipo associate *)
let etypeToType = function 
  |Etypename(BooleanType) -> BooleanType 
  |Etypename(IntegerType) -> IntegerType 
  |Etypename(StringType) -> StringType 
  | _ -> failwith("EtypeToType fail");;

(*Conversione da evT -> Exp*)
let switch_evTTOexp v =
  match v with
    (Bool b) -> (Ebool b)
  | (Int i) -> (Eint i)
  | (String s) -> (Estring s)
  | _ -> failwith("switch_evTTOexp fail")
;;


(*CONTAINS in set set un valore x*)
let contains (set : evT) (x : evT) : evT =
  match set with
  | SetVal(Set(lst, tl)) ->  if typeof x != tl then failwith ("type error") 
      else 
        (match lst with
           [] -> Bool false 
         | h::t -> if h = x then Bool true else if containlst lst x then Bool true
             else Bool false )
  | _ -> failwith ("Contains fail")
;;

(*INSERIMENTO in set set di valore x*) 
let insert( set : evT)( x :evT) : evT = 
  match set with
    (*Se l'insieme non ha elementi*) 
  |SetVal(Empty(lst)) -> if typeof x != lst then failwith("type error") 
      else SetVal(Set([x], typeof x)) 
          (*Se l'insieme ha già elementi controllo che non immetto duplicati*)
  |SetVal(Set(lst, tl)) ->  if typeof x != tl then failwith("type error") 
      else
      if (contains set x) = (Bool true) then set 
      else SetVal(Set(x::lst, typeof x))
;;  

(*RIMOZIONE elemento x da set set *)
let remove ( set : evT)( x :evT) : evT = 
  match set with 
  |SetVal(Empty(lst)) -> failwith("Remove fail") 
  |SetVal(Set(lst,tl)) ->
      if(typeof x) != tl then failwith("type error")
      else let rec frem z=
             match z with
             |[]->[]
             |h::t -> if h=x then t else h::(frem t) in let r = (frem lst) in 
        ( match r with 
          | []->SetVal(Empty(tl))
          | _->SetVal(Set(r,tl)) 
        )
  |_->failwith("Remove fail") 
;;          

(*UNIONE di set x e set y*) 
let union (x: evT) (y: evT) : evT =
  match (x, y) with 
  | (SetVal(Set(lstx, typex)), SetVal(Set(lsty, typey))) -> 
      if typex != typey then failwith ("type error") 
      else let rec fUn l1 l2 =			
             match l2 with
               [] -> l1
             | h :: t -> let s = insert l1 h in fUn s t in
        fUn x lsty 
  |  _, _ -> failwith("union fail")
;;

(*INTERZEZIONE di set x e set y*)
let intersection (x: evT) (y: evT) : evT =
  match (x, y) with 
  |(SetVal(Set(lstx, typex)), SetVal(Set(lsty, typey))) -> 
      if typex!=typey then failwith ("type error") 
      else let rec fInte l1 l2 = 
             match l1 with
               []->l2
             | h :: t -> if (contains y h) = (Bool true) then fInte t (insert l2 h) else fInte t l2 in 
        fInte lstx (SetVal(Empty(typex)))
  |_, _ -> failwith("intersection fail")   
;;

(*DIFFERENZA tra set x e set y*)
let difference (x: evT) (y: evT) : evT =
  match (x, y) with 
  |(SetVal(Set(lstx, typex)), SetVal(Set(lsty, typey))) -> 
      if typex!=typey then failwith ("type error") 
      else let rec fdiff l1 l2 = 
             match l1 with
             |[]->l2
             |h::t -> if (contains y h) =(Bool true) then fdiff t l2 else fdiff t (insert l2 h)
        in fdiff lstx (SetVal(Empty(typex)))
  |_,_ -> failwith("difference fail")   
;;


(*Controllo se set x è vuoto *)
let checkempty(x: evT) : evT =
  match x with 
  | SetVal(Empty(_)) -> Bool true
  | SetVal(Set(lstx,typex)) -> Bool false
  |_->failwith("checkeEmpty fail");;


(*Controllo se set y è sottoinsieme di set x *)
let checksubset (x: evT) (y: evT) : evT =
  match (x, y) with 
  |(SetVal(Empty(lstx)), SetVal(Empty(lsty))) -> Bool true
  |(SetVal(Set(lstx, typex)), SetVal(Empty(lsty))) -> Bool true
  |(SetVal(Empty(lstx)), SetVal(Set(lst2, tl2))) -> Bool false
  |(SetVal(Set(lstx, typex)), SetVal(Set(lsty, typey))) -> 
      if typex!=typey then failwith ("type error") 
      else let rec fSub l1 l2 = 
             match l2 with 
             | []-> Bool true
             | h :: t -> if (contains x h) =(Bool true) then fSub l1 t 
                 else Bool false in fSub lstx lsty
  |_,_-> failwith("checksubset fail")                   
;;

(*Restituisce MAX di set*)
let maxset (x: evT) : evT =
  let rec fmax ls max=
    match ls with
    |[] -> max
    |h::t -> if h > max then fmax t h 
        else fmax t max in 
  match x with 
  |SetVal(Set(hx :: tx, typex)) -> fmax tx hx 
  |_->failwith("maxset fail")
                
;;   

(*Restituisce MIN di set*)
let minset(x: evT) : evT =
  let rec fmin ls min=
    match ls with
    |[]->min 
    |h::t -> if h < min then fmin t h 
        else fmin t min in 
  match x with 
  |SetVal(Set(hx :: tx, typex)) -> fmin tx hx 
  |_->failwith("maxset fail")
                
;;


(*interprete*)
let rec eval (e : exp) (r : evT env) : evT = match e with
    Eint(n) -> Int n
  | Ebool(b) -> Bool b 
  | Estring(s) -> String s 
  | Etypename(st) -> String "" 
  | IsZero a -> iszero (eval a r) 
  | Den i -> applyenv r i
  | Eq(a, b) -> eq (eval a r) (eval b r) 
  | Prod(a, b) -> prod (eval a r) (eval b r) 
  | Sum(a, b) -> sum (eval a r) (eval b r)
  | Diff(a, b) -> diff (eval a r) (eval b r)
  | Minus a -> minus (eval a r)
  | And(a, b) -> et (eval a r) (eval b r) 
  | Or(a, b) -> vel (eval a r) (eval b r)
  | Not a -> non (eval a r)
  | Ifthenelse(a, b, c) -> 
      let g = (eval a r) in
      if (typecheck "bool" g) 
      then (if g = Bool(true) then (eval b r) else (eval c r))
      else failwith ("nonboolean guard") 
  | Let(i, e1, e2) -> eval e2 (bind r i (eval e1 r))
  | Fun(i, a) -> FunVal(i, a, r)
  | FunCall(f, eArg) -> 
      let fClosure = (eval f r) in
      (match fClosure with
         FunVal(arg, fBody, fDecEnv) -> 
           eval fBody (bind fDecEnv arg (eval eArg r)) |
         RecFunVal(g, (arg, fBody, fDecEnv)) -> 
           let aVal = (eval eArg r) in
           let rEnv = (bind fDecEnv g fClosure) in
           let aEnv = (bind rEnv arg aVal) in
           eval fBody aEnv |
         _ -> failwith("non functional value")) |
    Letrec(f, funDef, letBody) ->
      (match funDef with
         Fun(i, fBody) -> let r1 = (bind r f (RecFunVal(f, (i, fBody, r)))) in
           eval letBody r1 |
         _ -> failwith("non functional def"))
  |Singletone (set) -> 
      let a = eval set r in SetVal(Set([a], typeof a))  (*Set con un elemento*)
  |Emptyset (set) -> let tset=etypeToType set in
      SetVal(Empty(tset)) (* Set vuoto *)
  |Contains(a, b) -> 
      let a1 = eval a r in
      let b1 = eval b r in
      contains a1 b1
  |Insert(a, b) -> 
      let a1 = eval a r in
      let b1 = eval b r in
      insert a1 b1 
  |Remove(a, b) -> 
      let a1 = eval a r in
      let b1 = eval b r in
      remove a1 b1 
  |Union(a,b) ->
      let a1 = eval a r in
      let b1 = eval b r in
      union a1 b1 
  |Intersection(a,b) ->
      let a1 = eval a r in
      let b1 = eval b r in
      intersection a1 b1
  |Difference(a,b)->
      let a1 = eval a r in
      let b1 = eval b r in
      difference a1 b1
  |CheckEmpty(a) -> 
      let a1 = eval a r in
      checkempty a1
  |CheckSubset(a,b) -> 
      let a1 = eval a r in
      let b1 = eval b r in
      checksubset a1 b1
  |MinSet(a)->
      let a1 = eval a r in
      minset a1
  |MaxSet(a)->let a1 = eval a r in
      maxset a1
  |ForAll(pred, set) -> 
      let set1 = eval set r in
      (match set1 with
       |SetVal(Empty(_)) -> Bool true
       |SetVal(Set(lst, tp)) ->
           (match pred with
            |Fun(_,_) -> 
                let env0 = emptyenv Unbound in
                let rec checkPredExists l =
                  ( match l with
                    |h::t -> let fval = eval (FunCall(pred, (switch_evTTOexp h))) env0 in
                        if fval = Bool(true) then checkPredExists t else Bool(false)
                    |[]->Bool true )
                in checkPredExists lst
            |_ -> failwith("ForAll fail: predicate"))
       |_->failwith("ForAll fail : set")) 
  |Exists(pred,set)->
      let set1 = eval set r in
      (match set1 with 
       |SetVal(Empty(_)) -> Bool true
       |SetVal(Set(lst, tp)) ->
           (match pred with
            |Fun(_,_) -> 
                let env0 = emptyenv Unbound in
                let rec checkPredExists l =
                  ( match l with
                    |h::t -> let fval = eval (FunCall(pred, (switch_evTTOexp h))) env0 in
                        if fval = Bool(false) then checkPredExists t else Bool(true)
                    |[]->Bool false )
                in checkPredExists lst
            |_ -> failwith("Exists fail: predicate"))
       |_->failwith("Exists fail : set")) 
  |Map(func,set) ->
      let set1 = eval set r in
      (match set1 with 
       |SetVal(Set(lst, tp)) ->
           (match func with
            |Fun(_, _) ->let env0 = emptyenv Unbound in
                let rec checkFuncMap l acc= 
                  (match l with
                   |[]->acc
                   | h::t -> checkFuncMap t ((eval (FunCall(func, (switch_evTTOexp h))) env0)::acc))
                in SetVal(Set((checkFuncMap lst [], tp)))
            |_ -> failwith("Map fail: func"))
       |_->failwith("Map fail : set")) 
  |Filter(pred,set)->
      let set1 = eval set r in
      (match set1 with 
       |SetVal(Empty(_)) -> Bool true
       |SetVal(Set(lst, tp)) ->
           (match pred with
            |Fun(_,_) -> 
                let env0 = emptyenv Unbound in
                let rec checkPredFilter l acc =
                  (match l with
                   |[]->acc 
                   |h::t -> let fval = eval (FunCall(pred, (switch_evTTOexp h))) env0 in
                       if fval = Bool(true) then checkPredFilter t (h::acc) else checkPredFilter t acc)
                in SetVal(Set((checkPredFilter lst [], tp)))
            |_ -> failwith("Map fail: func"))
       |_->failwith("Map fail : set")) 
                
      
(* -----------------TEST SET -----------------------*)

let env = emptyenv Unbound;;
let es = Emptyset(Etypename(IntegerType));;
let rs1 = eval es env;;

(*Primo set*)

let set = Singletone(Eint(22)) ;;
let rs2 = eval set env ;;

let set = Insert(set, Eint 1) ;; 
let set = Insert(set, Eint 12) ;;
let set = Insert(set, Eint 13) ;;
(* deve contenere 22,1,12,13*)
let rs3 = eval set env ;;

(*SEcondo set*)
let set2 = Singletone(Eint(22)) ;;
let rs4 = eval set2 env ;;

let set2 = Insert(set2, Eint 14) ;;
let set2 = Insert(set2, Eint 15) ;;
let set2 = Insert(set2, Eint 16) ;;
let set2 = Insert(set2, Eint 17) ;; 
(* deve contenere 22,14,15,16,17*)
let rs5 = eval set2 env ;;

(*Terzo set*)
let set3 = Singletone(Eint(22)) ;;
let rs4 = eval set3 env ;;

let set3 = Insert(set3, Eint 14) ;;
let set3 = Insert(set3, Eint 15) ;;
let set3 = Insert(set3, Eint 16) ;;

(* deve contenere 22,14,15,16,17*)
let rs5 = eval set2 env ;;

(*Quarto set*)
let set4 = Singletone(Eint(0)) ;;
let set4 = Insert(set4, Eint 0) ;;
let set4 = Insert(set4, Eint 0) ;;

(* deve contenere 0*)
let rs6 = eval set4 env ;;



(*Primo set contiene 1? *)
eval(Contains(set, Eint 1)) env ;; (*True*)

(*Secondo set contiene 19? *)

eval(Contains(set2, Eint 19)) env ;; 
(*Unione=1,12,13,14,15,16,17,22*)
eval(Union(set, set2)) env;;

(*Intersezione=22*)
eval(Intersection(set, set2)) env;;

(*Differenza set set2=1,12,13 *)
eval(Difference(set, set2)) env;;

(*Differenza set2 set=14,15,16,17 *)
eval(Difference(set2, set)) env;;

(*Rimozione 14 da secondo set*)
eval(Remove(set2, Eint 14)) env ;;

(*Set 3 subset di set2?*) 
eval(CheckSubset(set2,set3)) env;; (*true*)

(*Set2 subset di set3?*)
eval(CheckSubset(set3,set2)) env;; (*false*)

(*Set 3 subset di set1?*) 
eval(CheckSubset(set3,set)) env;; (*false*)

(*FOR ALL=*)

(* per ogni x in set, x = 0 ?*)
eval(ForAll ((Fun("x", Ifthenelse(IsZero(Den "x"), Ebool true, Ebool false))), set)) env;; (* false *)
eval(ForAll ((Fun("x", Ifthenelse(IsZero(Den "x"), Ebool true, Ebool false))),set4)) env;; (* true *)

(* per ogni x in set, x = 1? *)
eval(ForAll ((Fun("x", Ifthenelse(Eq(Den "x",Eint 1), Ebool true, Ebool false))), set)) env;; (* false *) 
  
(*EXISTS=*)   
(*Esiste un elemento x in set, x=0?*)
eval(Exists ((Fun("x", Ifthenelse(IsZero(Den "x"), Ebool true, Ebool false))), set)) env;; (* false *)  
                                                                                           
eval(Exists ((Fun("x", Ifthenelse(IsZero(Den "x"), Ebool true, Ebool false))),set4)) env;; (* true *)

(*Esiste un elemento x in set, x=1?*)                                                                                     
eval(Exists ((Fun("x", Ifthenelse(Eq(Den "x",Eint 1), Ebool true, Ebool false))), set)) env;; (* true *)

(*MAP*)
(*Restituisce applicazione di funzione Sum*)
eval(Map(Fun("x", Sum(Den "x", Den "x")),set)) env;; (*44,2,24,26*) 
(*Restituisce applicazione di funzione Diff*)                                                                    
eval(Map(Fun("x", Diff(Den "x", Den "x")),set)) env;; (*0,0,0,0*)   
                                                      
(*FILTER*)
(*Elementi x con x =1 o x= 12*) 
eval(Filter ((Fun("x", Ifthenelse((Or(Eq(Den "x",Eint 1),Eq(Den "x",Eint 12)), Ebool true, Ebool false))), set))) env;; (* [1],[12] *)
           
eval(Filter ((Fun("x", Ifthenelse((Or(Eq(Den "x",Eint 1),Eq(Den "x",Eint 12)), Ebool true, Ebool false))), set3))) env;;(*[]*)                                                                               