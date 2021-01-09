type ide = string;;


(* Aggiunto tipo esprimibile Tset il quale rappresenta un insieme  di valori *)
type tval = TInt  
  | TBool                  | TString
  | Closure of tval * tval | RecClosure of tval * tval
  | Tset of string         | Unbound ;;

type texp = 
  | CstInt                | CstBool 
  | Or of texp * texp     | And of texp * texp       | Non of texp
  | Str of string         | StrEquals of texp * texp | Ifthenelse of texp * texp * texp
  | Sum of texp * texp    | Sub of texp * texp       | Times of texp * texp
  | Eq of texp * texp     | MinusThen of texp * texp | Greater of texp * texp
  | IsZero of texp        | Let of ide * texp * texp | Fun of ide * texp * texp
  | Apply of texp * texp  | Den of ide               | Letrec of ide * ide * tval * tval * texp * texp
(* Estenzione grammatica per la manipolazione di insiemi senza ordinamento e duplicati *)
  | EmptySet of string
  | SingleSet of string * texp | MultiSet of string * texp list | AddSet of texp * texp      | DelSet of texp * texp
  | IsEmptySet of texp         | ContainsSet of texp * texp     | MaxSet of texp             | MinSet of texp 
  | UnionSet of texp * texp    | DiffSet of texp * texp         | IntesectSet of texp * texp | SubsetSet of texp * texp
  | MapSet of texp * texp      | ForAllSet of texp * texp       | ExistSet of texp * texp    | FilterSet of texp * texp;;

type 'v env = (string * 'v) list;;

  
let emptyEnv  = [ ("", Unbound)] ;;

let bind (s: tval env) (i:string) (x:tval) = ( i, x ) :: s;;
  
let rec lookup (s:tval env) (i:string) = match s with
    | [] ->  Unbound
    | (j,v)::sl when j = i -> v
    | _::sl -> lookup sl i;;

let rec checker (e:texp) (env :tval env) =  match e with
      | CstInt -> TInt
      | CstBool  -> TBool
      | Str(a) -> TString
      | Let(i, e1, e2) -> let t = (checker e1 env) in (checker e2 (bind env i t))
      | Den(s) -> lookup env s
      | Fun(id,eIn,e) -> let tIn = (checker eIn env) in let tOut = (checker e (bind env id tIn)) in Closure(tIn,tOut)
      | Letrec(name,arg,tIn,tOu,e,letbody) -> let nenv = (bind env name (RecClosure(tIn,tOu))) in 
                                                let senv = (bind nenv arg tIn) in   
                                                  if (tOu = (checker e senv)) then (checker letbody senv) else failwith("type error")
      | Apply(e1, e2) -> (match (checker e1 env) with
                            | Closure(t1,t2) -> if ((checker e2 env) = t1) then t2 else failwith("type error")
                            | RecClosure(t1,t2) -> (match ((t1=t2),((checker e2 env) = t2)) with 
                                                      | (true,true) -> t1
                                                      | (_,_) -> failwith("type error"))
                            | _ -> failwith("type error"))
      | IsZero(e1) -> (match (checker e1 env) with
                        | TInt -> TBool
                        | _ -> failwith("type error"))
      | Or(e1, e2) -> (match ((checker e1 env),(checker e2 env)) with
                          | (TBool, TBool) -> TBool
                          | (_,_) -> failwith("type error"))
      | And(e1, e2) ->(match ((checker e1 env),(checker e2 env)) with
                          | (TBool, TBool) -> TBool
                          | (_,_) -> failwith("type error"))    
      | Non(e1) -> (match (checker e1 env) with
                          | TBool -> TBool
                          | _ -> failwith("type error"))                                              
      | Sum(e1, e2) -> (match ((checker e1 env),(checker e2 env)) with
                          | (TInt, TInt) -> TInt
                          | (_,_) -> failwith("type error"))
      | Times(e1, e2) -> (match ((checker e1 env),(checker e2 env)) with
                          | (TInt, TInt) -> TInt
                          | (_,_) -> failwith("type error"))
      | Sub(e1,e2) -> (match ((checker e1 env),(checker e2 env)) with
                          | (TInt, TInt) -> TInt
                          | (_,_) -> failwith("type error"))
      | Eq(e1, e2) -> (match ((checker e1 env),(checker e2 env)) with
                          | (TInt, TInt) -> TBool
                          | (_,_) -> failwith("type error"))
      | StrEquals(e1, e2) -> (match ((checker e1 env),(checker e2 env)) with
                          | (TString, TString) -> TBool
                          | (_,_) -> failwith("type error"))         
      | Ifthenelse(e1, e2, e3) -> (match (checker e1 env) with
                                    | TBool ->  let b1 = checker e2 env in if(b1 = (checker e3 env)) then b1
                                                                          else failwith("branch <if> e branch <else> must be same type")
                                    | _ -> failwith("<guard> nonboolean guard"))                           
      | MinusThen(e1,e2) -> (match ((checker e1 env),(checker e2 env)) with
                          | (TInt, TInt) -> TBool
                          | (_,_) -> failwith("type error"))    
      | Greater(e1,e2) -> (match ((checker e1 env),(checker e2 env)) with
                          | (TInt, TInt) -> TBool
                          | (_,_) -> failwith("type error"))
      (* se il tipo passato come parametro è corretto allora restituisce un insieme *)
      | EmptySet(tp) -> (match tp with 
                          | "int"    -> Tset("int")
                          | "bool"   -> Tset("bool")
                          | "string" -> Tset("string")
                          | _ -> failwith("type error"))
      (* Se gli l'argomenti hanno un tipo tra quelli permessi allora restituisce un insieme *)
      | SingleSet(t,arg) -> (match (t, (checker arg env) ) with 
                              | ("int",TInt) -> Tset("int")
                              | ("string",TString) -> Tset("string")
                              | ("bool",TBool) -> Tset("bool")
                              | (_,_) -> failwith("type error"))
      (* Come sopra *)
      | MultiSet(t,args) -> if (t = "int" || t = "string" || t = "bool" ) 
                                then  (match args with 
                                        | [] -> Tset(t) | a::b -> Tset(t)) (* il secondo argomento deve essere un lista *)
                                else failwith("type error")
      (* Se il parametro è un insieme allora, restituisce la veridicià del predicato *)
      | IsEmptySet(set) -> (match (checker set env) with 
                              | Tset(t) -> TBool
                              | _ -> failwith("type error"))
      (* Se è un insieme ed il valore ha il tipo tra quelli permessi, restituisce un nuovo insieme *)
      | AddSet(set,v) -> (match (checker set env) with
                            | Tset(t) -> (match (t,(checker v env)) with
                                          | ("int",TInt) -> Tset(t)
                                          | ("bool",TBool) -> Tset(t)
                                          | ("string",TString) -> Tset(t)
                                          | (_,_) ->failwith("type error"))
                            | _ -> failwith("type error"))
      (* Come sopra *)
      | DelSet(set,v) ->  (match (checker set env) with
                            | Tset(t) -> (match (t,(checker v env)) with
                                          | ("int",TInt) -> Tset(t)
                                          | ("bool",TBool) -> Tset(t)
                                          | ("string",TString) -> Tset(t)
                                          | (_,_) ->failwith("type error"))
                            | _ -> failwith("type error"))
      (* Se è un insieme ed il valore ha il tipo tra quelli permessi, restituisce la veridicià del predicato *)
      | ContainsSet(set,v) -> (match (checker set env) with
                            | Tset(t) -> (match (t,(checker v env)) with
                                          | ("int",TInt) -> TBool
                                          | ("bool",TBool) -> TBool
                                          | ("string",TString) -> TBool
                                          | (_,_) ->failwith("type error"))
                            | _ -> failwith("type error"))
      (* Se è un insieme allora restituisce un intero *)                                  
      | MaxSet(set) ->  (match (checker set env) with 
                            | Tset(i) when (i = "int") -> TInt
                            | _ -> failwith("type error"))    
      (* Come sopra *)                        
      | MinSet(set) -> (match (checker set env) with 
                            | Tset(i) when (i = "int") -> TInt
                            | _ -> failwith("type error"))
      (* Se entrambi sono degli insiemi allora ne restituisce un terzo *)
      | UnionSet(setA,setB) -> (match ((checker setA env), (checker setB env)) with 
                                | (Tset(i1),Tset(i2)) when (i1 = i2) -> Tset(i1)
                                | (_,_) -> failwith("type error"))  
      (* Come sopra *)                                      
      | DiffSet(setA,setB) -> (match ((checker setA env), (checker setB env)) with 
                                | (Tset(i1),Tset(i2)) when (i1 = i2) -> Tset(i1)
                                | (_,_) -> failwith("type error"))  
      (* Come sopra *)                                      
      | IntesectSet(setA,setB) -> (match ((checker setA env), (checker setB env)) with 
                                    | (Tset(i1),Tset(i2)) when (i1 = i2) -> Tset(i1)
                                    | (_,_) -> failwith("type error"))  
      (* Come sopra *)                                          
      | SubsetSet(setA,setB) -> (match ((checker setA env), (checker setB env)) with 
                                  | (Tset(i1),Tset(i2)) when (i1 = i2) -> Tset(i1)
                                  | (_,_) -> failwith("type error"))
      (* Se è una funzione ed un insieme, restituisce un nuovo insieme *)                                        
      | MapSet(ef,set) ->  (match ((checker ef env), (checker set env)) with 
                              | (Closure(t1,t2),Tset(i)) -> (match ((t1=t2),t1,i) with
                                                              | (true,TInt,"int") -> Tset(i)
                                                              | (true,TString,"string") -> Tset(i)
                                                              | (true,TBool,"bool") -> Tset(i)
                                                              | (_,_,_) -> failwith("type error")) 
                              | (_,_) -> failwith("type error"))
      (* Come sopra *)                                        
      | FilterSet(ef,set) -> (match ((checker ef env), (checker set env)) with 
                                | (Closure(t1,t2),Tset(i)) -> (match (t2,t1,i) with
                                                                | (TBool,TInt,"int") -> Tset(i)
                                                                | (TBool,TString,"string") -> Tset(i)
                                                                | (TBool,TBool,"bool") -> Tset(i)
                                                                | (_,_,_) -> failwith("type error")) 
                                | (_,_) -> failwith("type error"))
      (* Se è una funzione ed un insieme, restituisce la veridicirà del predicato *)                                        
      | ForAllSet(ef,set) -> (match ((checker ef env), (checker set env)) with 
                                | (Closure(t1,t2),Tset(i)) -> (match (t2,t1,i) with
                                                                | (TBool,TInt,"int") -> TBool
                                                                | (TBool,TString,"string") -> TBool
                                                                | (TBool,TBool,"bool") -> TBool
                                                                | (_,_,_) -> failwith("type error"))
                                | (_,_) -> failwith("type error"))
      (* Come sopra *)                                      
      | ExistSet(ef,set) -> (match ((checker ef env), (checker set env)) with 
                                | (Closure(t1,t2),Tset(i)) -> (match (t2,t1,i) with
                                                                | (TBool,TInt,"int") -> TBool
                                                                | (TBool,TString,"string") -> TBool
                                                                | (TBool,TBool,"bool") -> TBool
                                                                | (_,_,_) -> failwith("type error"))
                                | (_,_) -> failwith("type error")) ;;

let typeCheck e = checker e [];;


(* Tset *)
typeCheck (EmptySet("int"));;
typeCheck (EmptySet("string"));;
typeCheck (EmptySet("bool"));;

typeCheck (Let("x",CstBool,Or(Den("x"),CstBool)));;
(* Tset *)
typeCheck (SingleSet("int",Sum(CstInt,CstInt)));;

(* Tset *)
typeCheck (MultiSet("int",[Sum(CstInt,CstInt);CstInt]));;

(* Bool *)
typeCheck (IsEmptySet(MultiSet("int",[Sum(CstInt,CstInt);CstInt])));;

(* Tset *)
typeCheck (AddSet(MultiSet("int",[Sum(CstInt,CstInt);CstInt]),CstInt));;

(* Tset *)
typeCheck (DelSet(MultiSet("int",[Sum(CstInt,CstInt);CstInt]),CstInt));;

(* Bool *)
typeCheck (ContainsSet(MultiSet("int",[Sum(CstInt,CstInt);CstInt]),CstInt));;

(* Int *)
typeCheck (MaxSet(MultiSet("int",[Sum(CstInt,CstInt);CstInt])));;

(* Int *)
typeCheck (MinSet(MultiSet("int",[Sum(CstInt,CstInt);CstInt])));;

(* Tset *)
typeCheck (UnionSet(SingleSet("int",CstInt),SingleSet("int",CstInt)));;

(* Tset *)
typeCheck (DiffSet(SingleSet("int",CstInt),SingleSet("int",CstInt)));;

(* Tset *)
typeCheck (IntesectSet(SingleSet("int",CstInt),SingleSet("int",CstInt)));;

(* Bool *)
typeCheck (SubsetSet(SingleSet("int",CstInt),SingleSet("int",CstInt)));;

(* Tset *)
typeCheck (MapSet(Fun("x",CstInt,CstInt),SingleSet("int",CstInt)));;

(* Bool *)
typeCheck (ForAllSet(Fun("x",CstInt,CstBool),SingleSet("int",CstInt)));;

(* Bool *)
typeCheck (ExistSet(Fun("x",CstInt,CstBool),SingleSet("int",CstInt)));;

(* Tset *)
typeCheck (FilterSet(Fun("x",CstInt,CstBool),SingleSet("int",CstInt)));;

typeCheck (Letrec("fact","n",TInt,TInt,
                  Ifthenelse(Eq(Den("n"),CstInt),
                  CstInt,
                  Times(Den("n"),Apply(Den("fact"),Sub(Den("n"),CstInt)))), Apply(Den("fact"),CstInt)));;