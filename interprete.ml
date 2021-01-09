(* The language *)
type ide = string;;
type exp = 
    CstInt of int     | CstTrue                | CstFalse 
   | Or of exp * exp  | And of exp * exp       | Non of exp
   | Str of string    | StrEquals of exp * exp | Ifthenelse of exp * exp * exp
   | Sum of exp * exp | Sub of exp * exp       | Times of exp * exp
   | Eq of exp * exp  | MinusThen of exp * exp | Greater of exp * exp
   | IsZero of exp    | Let of ide * exp * exp | Letrec of ide * ide * exp * exp 
   | Den of ide       | Fun of ide * exp       | Apply of exp * exp
(* Estenzione grammatica per la manipolazione di insiemi senza ordinamento e senza duplicati *)
  | EmptySet of string
  | SingleSet of string * exp | MultiSet of string * exp list | AddSet of exp * exp       | DelSet of exp * exp
  | IsEmptySet of exp         | ContainsSet of exp * exp      | MaxSet of exp             | MinSet of exp 
  | UnionSet of exp * exp     | DiffSet of exp * exp          | IntesectSet of exp * exp  | SubsetSet of exp * exp
  | MapSet of exp * exp       | ForAllSet of exp * exp        | ExistSet of exp * exp     | FilterSet of exp * exp;;
  
type 'v env = (string * 'v) list;;

(* Aggiunto tipo esprimibile Set il quale rappresenta un insieme di valori rappresentato come una coppia <tipo di valore ,lista di valori>  *)
type evT = Int of int 
  | Bool of bool                   | String of string
  | Closure of ide * exp * evT env | RecClosure of ide * ide * exp * evT env 
  | Set of string * evT list       | Unbound ;;

let emptyEnv  = [ ("", Unbound)] ;;

let bind (s: evT env) (i:string) (x:evT) = ( i, x ) :: s;;

let rec lookup (s:evT env) (i:string) = match s with
    | [] ->  Unbound
    | (j,v)::sl when j = i -> v
    | _::sl -> lookup sl i;;

let typecheck (x, y) = match x with	
                        | "int" ->    (match y with | Int(u) -> true | _ -> false)
                        | "bool" ->   (match y with | Bool(u) -> true | _ -> false)
                        | "string" -> (match y with | String(u) -> true | _ -> false)
                        | _ -> failwith ("not a valid type");;

let int_eq(x,y) =  match (typecheck("int",x), typecheck("int",y), x, y) with
                    | (true, true, Int(v), Int(w)) -> Bool(v = w)
                    | (_,_,_,_) -> failwith("run-time error ");;

let str_eq(x,y) =  match (typecheck("string",x), typecheck("string",y), x, y) with
                    | (true, true, String(v), String(w)) -> Bool(v = w)
                    | (_,_,_,_) -> failwith("run-time error ");;

let int_minusthan(x,y) =  match (typecheck("int",x), typecheck("int",y), x, y) with
                          | (true, true, Int(v), Int(w)) -> Bool(v < w)
                          | (_,_,_,_) -> failwith("run-time error ");;      

let int_greater(x,y) =  match (typecheck("int",x), typecheck("int",y), x, y) with
                        | (true, true, Int(v), Int(w)) -> Bool(v > w)
                        | (_,_,_,_) -> failwith("run-time error ");;
  
let int_plus(x, y) = match(typecheck("int",x), typecheck("int",y), x, y) with
                        | (true, true, Int(v), Int(w)) -> Int(v + w)
                        | (_,_,_,_) -> failwith("run-time error ");;

let int_sub(x, y) = match(typecheck("int",x), typecheck("int",y), x, y) with
                        | (true, true, Int(v), Int(w)) -> Int(v - w)
                        | (_,_,_,_) -> failwith("run-time error ");;

let int_times(x, y) = match(typecheck("int",x), typecheck("int",y), x, y) with
                        | (true, true, Int(v), Int(w)) -> Int(v * w)
                        | (_,_,_,_) -> failwith("run-time error ");;

let bool_and(x, y) = match(typecheck("bool",x),typecheck("bool",y),x,y) with
                        | (true,true,Bool(b),Bool(e)) -> Bool(b && e)
                        | (_,_,_,_) -> failwith("run-time error ");;

let bool_or(x, y) = match(typecheck("bool",x),typecheck("bool",y),x,y) with
                        | (true,true,Bool(b),Bool(e)) -> Bool(b || e)
                        | (_,_,_,_) -> failwith("run-time error ");;

let is_Zero(x) = match(typecheck("int",x),x) with
                  | (true,Int(n)) -> Bool(n=0)
                  | (_,_) -> failwith("run-time error ");;

let non(x) = match(typecheck("bool",x),x) with
              | (true,Bool(true))  -> Bool(false)
              | (true,Bool(false)) -> Bool(true)
              | (_,_) -> failwith("run-time error ");;

(* Effettua una ricerca ricorsiva dell tipo esprimibile in una lista di esprimbili *)
let rec delItem (e:evT) (l:evT list) = match l with 
   | [] -> []  | a::b -> if(e = a) then b else a::(delItem e b) ;;

(* Restituisce una nuova lista aggiungendo in nuovo elemento se non è presente, altrimenti restituisce la lista passata inizialmente *)
let rec addItem (e:evT) (l:evT list) = match l with 
   | [] -> [e] | a::b -> if (a = e) then a::b else a::(addItem e b);;

let rec fndItem (e:evT) (l:evT list) = match l with 
   | [] -> false | a::b -> if (a = e) then true else fndItem e b;;

(* Scorre tutta la lista in modo ricorsivo portandosi dietro il valore più grande fino a quel punto trovato *)
let rec recmaxI (e:evT) (l:evT list) = match l with 
  | [] -> e | a::b -> if(e > a) then recmaxI e b else recmaxI a b;;

(* Scorre tutta la lista in modo ricorsivo portandosi dietro il valore più piccolo fino a quel punto trovato *)
let rec recminI (e:evT) (l:evT list) = match l with 
  | [] -> e | a::b -> if(e < a) then recminI e b else recminI a b;; 

(* Dati due insiemi, formati da valori non duplicati , ne costruisce un terzo aggiungendo tutti gli elementi della lista1 nell'insieme list2, ovviamente se non è già presente *)
let rec unionsetf (l1: evT list) (l2: evT list) = match l1 with 
  | [] -> l2 | a::b -> unionsetf b (addItem a l2);;

(* Dati due insiemi, ne costruisce un terzo rimuovendo tutti gli "eventuali" elementi della lista1 nell'insieme list2 *)
let rec diffsetf  (l1: evT list) (l2: evT list) = match l1 with 
  | [] -> l2 | a::b -> diffsetf b  (delItem a l2);;    

(* Dato un insieme effettua l'ordinamento "bubble sort". Utilizzato per effetturare l'intesezione di due insiemi 
   Funzionamento -> se la lista ha almeno un 2 elementi, porta il più grande a dx, ed effettua l'ordiamento,ricorsivo, tralasciando l'elemento più a sx
                    dopo aver effettuato n-1 scambi avremo il valore più grande a dx, ed effettuaiamo l'ordiamento per i valori a sx, tralasciando l'elemento più grande. *)
let rec sort (l:evT list) =
  let sorted = match l with
    | h1::h2::tl ->
        if (h1 > h2) then  h2::(sort (h1::tl)) else  h1::(sort (h2::tl))
    | tl -> tl
  in  if l = sorted then l else (sort sorted) ;;

(* Dati due insiemi ordinati, ne crea un terzo formato solo da gli elementi in comune 
  Funzionamento -> date due liste ordinate si confronta il valori più piccoli di entrabe le liste ,e di scorre una lista piuttosto che un altra in base ai valori trovati,
                    quando i primi due numeri corrispondono lo mantengo nella lista di intersezinone *)
let rec intersect (l1:evT list) (l2:evT list) = match l1 with 
  | [] -> []
  | h1::t1 -> ( match l2 with 
                  | [] -> []
                  | h2::t2 when h1 < h2 -> (intersect t1 l2)
                  | h2::t2 when h1 > h2 -> (intersect l1 t2)
                  | h2::t2 -> ( match (intersect t1 t2) with 
                        | [] -> [h1]
                        | h3::t3 as l when h3 = h1 -> l
                        | h3::t3 as l -> h1::l));;

(* Controlla se un insimeA è un sottoinsieme dell l'insiemeB, ovvero quando per ogni elemento di A è presente in B *)
let rec checksubset (l1:evT list) (l2:evT list) = match l1 with  
  | [] -> true
  | h::t when (fndItem h l2) -> (checksubset t l2)
  | h::t -> false ;;

let maxItem (l: evT list) = match l with 
  | [] -> Unbound | a::b -> recmaxI a b ;;

let minItem (l: evT list) = match l with 
  | [] -> Unbound | a::b -> recminI a b ;;   

  
(*  ---------------------------------------- INTERPRETE  ----------------------------------------  *)
(*  ---------------------------------------- INTERPRETE  ----------------------------------------  *)
(*  ---------------------------------------- INTERPRETE  ----------------------------------------  *)

let rec eval  (e:exp) (s:evT env) = match e with
  | CstInt(n) -> Int(n)
  | CstTrue -> Bool(true)
  | CstFalse -> Bool(false)
  | Str(a) -> String(a) 
  | IsZero(e) -> is_Zero(eval e s)
  | And(e1, e2) -> bool_and((eval e1 s),(eval e2 s))
  | Or(e1, e2) -> bool_or((eval e1 s),(eval e2 s))
  | Non(e) -> non(eval e s)
  | Eq(e1, e2)  -> int_eq((eval e1 s), (eval e2 s))
  | StrEquals(e1,e2) -> str_eq((eval e1 s), (eval e2 s))
  | MinusThen(e1,e2) -> int_minusthan((eval e1 s), (eval e2 s))
  | Greater(e1,e2) -> int_greater((eval e1 s), (eval e2 s))
  | Times(e1,e2) -> int_times((eval e1 s), (eval e2 s))
  | Sum(e1, e2) -> int_plus((eval e1 s), (eval e2 s))
  | Sub(e1, e2) -> int_sub((eval e1 s), (eval e2 s))
  | Ifthenelse(e1,e2,e3) -> let g = eval e1 s in
                              (match (typecheck("bool", g), g) with
			                          | (true, Bool(true)) -> eval e2 s
                                | (true, Bool(false)) -> eval e3 s
                	              | (_, _) -> failwith ("nonboolean guard"))
  | Den(i) -> lookup s i
  | Let(i, e, ebody) -> eval ebody (bind s i (eval e s))
  | Fun(arg, ebody) -> Closure(arg,ebody,s)
  | Letrec(f, arg, fBody, letBody) ->  let benv = bind (s) (f) (RecClosure(f, arg, fBody,s)) in eval letBody benv
  | Apply(eF, eArg) -> let fclosure = eval eF s in 
                        (match fclosure with 
                          | Closure(arg, fbody, fDecEnv) -> let aVal = eval eArg s in
	                                                              let aenv = bind fDecEnv arg aVal in eval fbody aenv
                          | RecClosure(f, arg, fbody, fDecEnv) -> let aVal = eval eArg s in
                                                                      let rEnv = bind fDecEnv f fclosure in
	                                                                        let aenv = bind rEnv arg aVal in eval fbody aenv
                          | _ -> failwith("non functional value"))
  (* Creo un insieme vuoto, definendone il tipo degli elementi, che possono essere interi, stringhe o booleani, altrimenti genero un eccezione *)
  | EmptySet(tp) -> (match tp with  
                      | "int" -> Set("int",[])
                      | "bool" -> Set("bool",[])
                      | "string" -> Set("string",[])
                      | _  -> failwith("type not allowed or Unbound"))
  (* Creo un insieme partendo da un elemento passato come parametro, la valutazione dell'espressione mi dovrà restituire lo stesso tipo di quello dichirato *)
  | SingleSet(tp,arg) -> let xVal = (eval arg s) in (match (tp,typecheck(tp,xVal)) with 
                                                      | ("int",true)    -> Set("int",[xVal])
                                                      | ("bool",true)   -> Set("bool",[xVal])
                                                      | ("string",true) -> Set("string",[xVal])
                                                      | (_,_)  -> failwith("type not allowed or Unbound"))
  (* Creo un insieme partendo da una lista di espressioni, la valutazione della lista mi dovrà restituire valori dello stesso tipo ed conformi a quello dichiarato. *)
  | MultiSet(tp,args) -> (match tp with  
                            | "int" ->  Set("int", (evaList args [] "int" s)) 
                            | "bool" -> Set("bool", (evaList args [] "bool" s))   
                            | "string" -> Set("string", (evaList args [] "string" s))  
                            | _  -> failwith("type not allowed or Unbound"))
  (* Restituisce un'insiemeB formato da l'insiemeA passato come paramentro ed un nuovo valore ,sempre conforme al tipo di l'insiemeA di partenza *)
  | AddSet(set,arg) -> (match (eval set s) with  (* Valuto l'elemento da aggiungere, ogni elemento nella lista è un tipo esprimibile *)
                          | Set(tp,vals) -> let xVal = (eval arg s) in (* Se il paramentro è un insieme ed il tipo è corretto allora crea un nuovo insieme con il nuovo valore, se già presente lo ignora *)
                                              if(typecheck(tp,xVal)) then Set(tp,addItem xVal vals) else failwith("Cannot Add Item with different type")
                          | _ -> failwith("No Set value"))
  | DelSet(set,arg) -> (match (eval set s) with (* Ragionamento analogo, solo che creo un nuovo insieme senza l'elemento arg, se presente *)
                          | Set(tp,vals) -> let xVal = (eval arg s) in 
                                              if(typecheck(tp,xVal)) then Set(tp,delItem xVal vals) else failwith("Argument isn't same type of set") 
                          | _ -> failwith("No Set value"))
  | IsEmptySet(set) -> (match (eval set s) with (* Verifica se set è un insieme *)
                          | Set(tp,vals) -> (match vals with | [] -> Bool(true) | _ -> Bool(false))
                          | _ -> failwith("No Set value"))
  | ContainsSet(set,arg) -> (match (eval set s) with  (* Verifica se set è un insieme *)
                          | Set(tp,vals) -> Bool( fndItem (eval arg s) vals ) (* Cerca il valore valutato, nella lista dei valori del set *)
                          | _ -> failwith("No Set value"))
  | MaxSet(set) -> (match eval set s with (*  Restituisce il valore intero più grande, oss. l'insieme deve essere necessariamente di tipo intero *)
                          | Set(tp,vals) -> (match tp with "int" -> (maxItem vals) | _ -> failwith("Cannot use Max function with no int type"))
                          | _ -> failwith("No Set value"))
  | MinSet(set) ->  (match eval set s with
                          | Set(tp,vals) -> (match tp with "int" -> (minItem vals) | _ -> failwith("Cannot use Min function with no int type"))
                          | _ -> failwith("No Set value")) 
  (* Dati due insiemi ne restituisce un terzo formato dall'unione dei due , rimuovendo i duplicati *)
  | UnionSet(setA,setB) -> (match ((eval setA s),(eval setB s)) with (* se entrambi gli argomenti sono dei Set ed hanno lo stesso tipo, altrimenti genero l'eccezione *)
                                | (Set(tpA,valsA),Set(tpB,valsB)) -> if (tpA = tpB) then (Set(tpA,unionsetf valsA valsB)) else failwith("Types don't match")
                                | (_,_) -> failwith("No Set Values"))
  (* Dato due insiemi A e B , rimuovo "eventualmente" tutti gli elementi di B che sono presenti in A *)
  | DiffSet(setA,setB) -> (match ((eval setA s),(eval setB s)) with
                                | (Set(tpA,valsA),Set(tpB,valsB)) -> if (tpA = tpB) then (Set(tpA,diffsetf valsA valsB)) else failwith("Types don't match")
                                | (_,_) -> failwith("No Set Values"))
  (* Dati due insiemi A e B , effetto l'intersezione dei due, ordinandoli prima *)
  | IntesectSet(setA,setB) -> (match ((eval setA s),(eval setB s)) with
                                | (Set(tpA,valsA),Set(tpB,valsB)) -> (match (tpA,tpB) with 
                                                                        | ("int","int") -> Set(tpA,(intersect (sort valsA) (sort valsB)))
                                                                        | ("string","string") -> Set(tpA,(intersect (sort valsA) (sort valsB)))
                                                                        | (_,_) -> failwith("Cannot use Intersect function with this type"))
                                | (_,_) -> failwith("No Set Values"))
   (* Dati due insiemi A e B ,verifico se ogni elemento di A sia presente in B *)
  | SubsetSet(setA,setB) ->  (match ((eval setA s),(eval setB s)) with
                                | (Set(tpA,valsA),Set(tpB,valsB)) -> (match (tpA,tpB) with 
                                                                        | ("int","int") -> Bool(checksubset valsA valsB)
                                                                        | ("string","string") ->  Bool(checksubset valsA valsB)
                                                                        | (_,_) -> failwith("Cannot use Subset function with this type"))
                                | (_,_) -> failwith("No Set Values"))
  (* Prendo come argomento una funzione ed un set, ed applico la funzione ad ogni elemento del set *)
  | MapSet(efn,set) -> (match ((eval efn s),(eval set s)) with 
                            | (Closure(arg, fbody, fDecEnv),Set(tp,l))-> Set(tp, (maplist arg fbody fDecEnv tp l )) (* Richiamo la funzione ausiliaria che effettua la map *)
                            | (_,_) -> failwith("No set Value or No fun value"))
  (*Verifico se ogni elemento dell'insieme rende vera l'applicazione della funzione *)
  | ForAllSet(efn,set) -> (match ((eval efn s),(eval set s)) with 
                            | (Closure(arg, fbody, fDecEnv),Set(tp,l))-> Bool(forallist arg fbody fDecEnv l)
                            | (_,_) -> failwith("No set Value or No fun value"))    
  (* Verifico esiste elemento dell'insieme rende vera l'applicazione della funzione *)                            
  | ExistSet(efn,set) -> (match ((eval efn s),(eval set s)) with 
                            | (Closure(arg, fbody, fDecEnv),Set(tp,l))-> Bool(exsistlist arg fbody fDecEnv l)
                            | (_,_) -> failwith("No set Value or No fun value"))     
 (* Restituisco un nuovo set con solo gli elementi che rendono vera l'applicazione della funzione *)                            
 | FilterSet(efn,set) -> (match ((eval efn s),(eval set s)) with 
                            | (Closure(arg, fbody, fDecEnv),Set(tp,l))-> Set(tp, (filterlist arg fbody fDecEnv l ))
                            | (_,_) -> failwith("No set Value or No fun value"))    


(* ------------- FUNZIONI AUSILIARIE ------------- *)  

(* Passati come parametri la "lista di espressioni da valutare" , "la lista valutata" , "il tipo che ogni espressione deve seguire" ,"l'ambiente per i riferimenti non locali" *)                     
and evaList (args: exp list) (l: evT list) (tp: string) (s: evT env)  = (match args with
                                                                          | [] -> l 
                                                                          | a::b -> let xVal = (eval a s) in  (* Valuto il primo valore, se il tipo non matcha allora genero un eccezione *)
                                                                              if(typecheck(tp,xVal)) then (evaList b (addItem xVal l) tp s) (* Valuto il resto della lista, aggiungendo il valore alla lista valutata *)
                                                                                                      else failwith("MultiSet:Items must have correct type"))
(* Passati come parametri i valori della chiusura, ossia : "il parametro della funzione",
   il "body della funzione" ,"ambiente corrente" , il "tipo corretto" che la funzione mi deve restituire e la "lista" mappata dalla funzione *)
and maplist (arg:ide) (fbody:exp) (s:evT env) (tp:string) (l:evT list) = (match l with
                    | [] -> []
                    | h::t -> let mapped = (eval fbody (bind s arg h)) in (* recupero il primo valore della lista, associo la coppia <valore,argomento> nell' ambiente corrente
                                                                             valuto il body della funzione con l'ambiente esteso, e controllo che il valore risultante sia conforme al tipo dell'insieme *)
                                    if(typecheck(tp,mapped)) then mapped::(maplist arg fbody s tp t) else failwith("Map: Map function return incorrect type"))
(* Come sopra *)
and forallist (arg:ide) (fbody:exp) (s:evT env) (l:evT list) = (match l with
                    | [] -> true  
                    | h::t -> let r = (eval fbody (bind s arg h)) in (match (typecheck("bool",r),r) with (* il valore risutante della funzione mi deve restituire necessariamente un valore booleano *)
                                                                            | (true,Bool(true))  -> (forallist arg fbody s t)
                                                                            | (true,Bool(false)) -> false (* un elemento non rispetta il predicato *)
                                                                            | (_,_) -> failwith("ForAll : predicate function is nonboolean guard")))
(* Come sopra *)
and exsistlist (arg:ide) (fbody:exp) (s:evT env) (l:evT list) = (match l with
                    | [] -> false 
                    | h::t -> let r = (eval fbody (bind s arg h)) in (match (typecheck("bool",r),r) with
                                                                | (true,Bool(true)) -> true (* esiste un elemento rispetta il predicato *)
                                                                | (true,Bool(false)) -> (exsistlist arg fbody s t)
                                                                | (_,_) -> failwith("Exsist: predicate function is nonboolean guard")))
(* Come sopra *)                                                               
and filterlist (arg:ide) (fbody:exp) (s:evT env) (l:evT list) = (match l with
                    | [] -> []
                    | h::t -> let r = (eval fbody (bind s arg h)) in (match (typecheck("bool",r),r) with
                                                                | (true,Bool(true)) -> h::(filterlist arg fbody s t) (* se il predicato viene rispettato allora creo una terza listo con questo elemento *)
                                                                | (true,Bool(false)) -> (filterlist arg fbody s t) (* altrimenti no *)
                                                                | (_,_) -> failwith("Filer, Filter function return incorrent type")));;



(*  ---------------------------------------- TESTING  ----------------------------------------  *)
(*  ---------------------------------------- TESTING  ----------------------------------------  *)
(*  ---------------------------------------- TESTING  ----------------------------------------  *)

(* insieme vuoto *)
let intset = EmptySet("int") in eval intset emptyEnv ;; 
let strset = EmptySet("string") in  eval strset emptyEnv ;;

(* insieme con un elemento *)
let intset = SingleSet("int",Sum(CstInt(3),CstInt(6))) in eval intset emptyEnv ;;
let strset = SingleSet("string",Str("ciao")) in eval strset emptyEnv ;;

(* insieme con una list di espressioni*)
let intset = MultiSet("int",[Sum(CstInt(3),CstInt(6));CstInt(19)]) in eval intset emptyEnv ;; 
let strset = MultiSet("string",[Str("ciao");Str("buongiorno")]) in eval strset emptyEnv ;;

 (* insieme con dei valori duplicati che vengono ignorati *)
let intset = MultiSet("int",[Sum(CstInt(3),CstInt(6));CstInt(19);CstInt(19)]) in eval intset emptyEnv ;;
let strset = MultiSet("string",[Str("ciao");Str("buongiorno");Str("ciao");]) in eval strset emptyEnv ;; 

(* Aggiunta di un valore ad un insieme *)
let intset = MultiSet("int",[Sum(CstInt(3),CstInt(6));CstInt(19)]) in let set2 = AddSet(intset,CstInt(45)) in eval set2 emptyEnv;; 
let strset = MultiSet("string",[Str("ciao");Str("buongiorno")]) in let set2 = AddSet(strset,Str("buonasera")) in eval set2 emptyEnv ;;

(* Rimozione di un valore da un insieme *)
let intset = MultiSet("int",[Sum(CstInt(3),CstInt(6));CstInt(19)]) in let set2 = DelSet(intset,Times(CstInt(2),CstInt(3))) in eval set2 emptyEnv;; 

let strset = MultiSet("string",[Str("ciao");Str("buongiorno")]) in let set2 = DelSet(strset,Str("ciao")) in eval set2 emptyEnv ;;

(* Verifica se un insieme è vuoto -> false *)
let intset = MultiSet("int",[Sum(CstInt(3),CstInt(6));CstInt(19)]) in let set2 = IsEmptySet(intset) in eval set2 emptyEnv;;

let strset = MultiSet("string",[Str("ciao");Str("buongiorno")]) in let set2 = IsEmptySet(strset) in eval set2 emptyEnv ;;

(* Verifica se un insieme è vuoto -> true *)
let intset = EmptySet("int") in let set2 = IsEmptySet(intset) in eval set2 emptyEnv;;

let strset = EmptySet("string") in let set2 = IsEmptySet(strset) in eval set2 emptyEnv ;;

(* Verifica se un elemento appartiene ad un insieme -> true *)
let intset = MultiSet("int",[Sum(CstInt(3),CstInt(6));CstInt(20)]) in let set2 = ContainsSet(intset,Sum((CstInt(19),CstInt(1)))) in eval set2 emptyEnv;;

let strset = MultiSet("string",[Str("ciao");Str("buongiorno")]) in let set2 = ContainsSet(strset,Str("ciao")) in eval set2 emptyEnv ;;

(* Verifica se un elemento appartiene ad un insieme -> false *)
let intset = MultiSet("int",[Sum(CstInt(3),CstInt(6));CstInt(19)]) in let set2 = ContainsSet(intset,CstInt(39)) in eval set2 emptyEnv;;

let strset = MultiSet("string",[Str("ciao");Str("buongiorno")]) in let set2 = ContainsSet(strset,Str("pomodoro")) in eval set2 emptyEnv ;;

(* Massimo elemento di un insieme *)
let intset = MultiSet("int",[CstInt(3);CstInt(6);CstInt(19);CstInt(118)]) in let max = MaxSet(intset) in eval max emptyEnv ;;

let strset = MultiSet("string",[Str("ciao");Str("buongiorno")]) in let set2 = MaxSet(strset) in eval set2 emptyEnv ;;

(* Minimo elemento di un insieme *)
let intset = MultiSet("int",[CstInt(3);CstInt(6);CstInt(19);CstInt(118)]) in let min = MinSet(intset) in eval min emptyEnv ;;

(* Unione due insiemi , senza duplicati *)
let intset = MultiSet("int",[CstInt(3);CstInt(6);CstInt(19);CstInt(118)]) in
    let intset2 = MultiSet("int",[CstInt(17);CstInt(14);CstInt(19);CstInt(8)]) in let set2 = UnionSet(intset,intset2) in eval set2 emptyEnv ;;

let strset = MultiSet("string",[Str("ciao");Str("buongiorno");Str("pomodori");Str("barcellona")]) in 
  let strset2 = MultiSet("string",[Str("auto");Str("ciao");Str("federico");Str("cuffie")]) in let set2 = UnionSet(strset,strset2) in eval set2 emptyEnv ;;

(* Diffenza due insiemi *)
let intset = MultiSet("int",[CstInt(3);CstInt(6);CstInt(19);CstInt(118)]) in
    let intset2 = MultiSet("int",[CstInt(17);CstInt(14);CstInt(19);CstInt(8)]) in let set2 = DiffSet(intset,intset2) in eval set2 emptyEnv ;;

let strset = MultiSet("string",[Str("ciao");Str("buongiorno");Str("pomodori");Str("barcellona")]) in 
  let strset2 = MultiSet("string",[Str("auto");Str("ciao");Str("federico");Str("cuffie")]) in let set2 = DiffSet(strset,strset2) in eval set2 emptyEnv ;;

(* Itersezione due insiemi *)
let intset = MultiSet("int",[CstInt(3);CstInt(6);CstInt(19);CstInt(118)]) in
    let intset2 = MultiSet("int",[CstInt(17);CstInt(14);CstInt(19);CstInt(8)]) in let set2 = IntesectSet(intset,intset2) in eval set2 emptyEnv ;;

let strset = MultiSet("string",[Str("ciao");Str("buongiorno");Str("pomodori");Str("barcellona")]) in 
  let strset2 = MultiSet("string",[Str("auto");Str("ciao");Str("federico");Str("cuffie")]) in let set2 = IntesectSet(strset,strset2) in eval set2 emptyEnv ;;

(* Verfico se il primo insieme e una sotto-sequenza del secondo -> true *)
let intset = MultiSet("int",[CstInt(3);CstInt(6);CstInt(19)]) in
    let intset2 = MultiSet("int",[CstInt(19);CstInt(3);CstInt(6);CstInt(89)]) in let set2 = SubsetSet(intset,intset2) in eval set2 emptyEnv ;;

let strset = MultiSet("string",[Str("ciao");Str("federico");Str("auto")]) in 
  let strset2 = MultiSet("string",[Str("auto");Str("ciao");Str("federico");Str("cuffie")]) in let set2 = SubsetSet(strset,strset2) in eval set2 emptyEnv ;; 
  
(* Verfico se il primo insieme e una sotto-sequenza del secondo -> false *)
let intset = MultiSet("int",[CstInt(3);CstInt(6);CstInt(29)]) in
    let intset2 = MultiSet("int",[CstInt(19);CstInt(3);CstInt(6);CstInt(92)]) in let set2 = SubsetSet(intset,intset2) in eval set2 emptyEnv ;;

let strset = MultiSet("string",[Str("ciao");Str("federico");Str("auto")]) in 
  let strset2 = MultiSet("string",[Str("auto");Str("ciao");Str("marcello");Str("cuffie")]) in let set2 = SubsetSet(strset,strset2) in eval set2 emptyEnv ;; 

(* Applico la map, moltiplico di 2 ogni intero nell' insieme *)
let intset = MultiSet("int",[CstInt(3);CstInt(6);CstInt(19);CstInt(118)]) in let max = MapSet(Fun("x",Times(Den("x"),CstInt(2))),intset) in eval max emptyEnv ;;

(* Controllo se ogni elemento dell'insieme è miore di 970 *)
let intset = MultiSet("int",[CstInt(3);CstInt(6);CstInt(19);CstInt(118)]) in let max = ForAllSet(Fun("x",MinusThen(Den("x"),CstInt(970))),intset) in eval max emptyEnv ;;

(* Controllo se esiste elemento dell'insieme che è maggiore di 970 *)
let intset = MultiSet("int",[CstInt(3);CstInt(6);CstInt(19);CstInt(118)]) in let max = ExistSet(Fun("x",Greater(Den("x"),CstInt(845))),intset) in eval max emptyEnv ;;

(* Controllo se esiste elemento dell'insieme tale che è uguale a "milan" -> false *)
let strset = MultiSet("string",[Str("ciao");Str("buongiorno");Str("milano");Str("pennarello");Str("matita")]) in 
  let set2 = ExistSet(Fun("x",StrEquals(Den("x"),Str("milan"))),strset) in eval set2 emptyEnv ;;

(* Controllo se esiste elemento dell'insieme tale che è uguale a "milano" -> false *)
let strset = MultiSet("string",[Str("ciao");Str("buongiorno");Str("milano");Str("pennarello");Str("matita")]) in 
  let set2 = ExistSet(Fun("x",StrEquals(Den("x"),Str("milano"))),strset) in eval set2 emptyEnv ;;

(* Restituisco solo gli elemento maggiori di 10 *)
let intset = MultiSet("int",[CstInt(3);CstInt(6);CstInt(19);CstInt(118)]) in let max = FilterSet(Fun("x",Greater(Den("x"),CstInt(10))),intset) in eval max emptyEnv ;;

(* Restituisco i valori dell' insieme se sono uguali a "milano" *)
let strset = MultiSet("string",[Str("ciao");Str("buongiorno");Str("milano");Str("pennarello");Str("matita")]) in 
  let set2 = FilterSet(Fun("x",StrEquals(Den("x"),Str("milano"))),strset) in eval set2 emptyEnv ;;