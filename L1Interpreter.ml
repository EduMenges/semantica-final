(* Auxiliares *)

(* Dado uma lista de pares, pesquisa pela chave e retorna o valor *)
let rec lookup amb key =
  match amb with
  | [] ->
      None
  | (head, item) :: tl ->
      if head = key then Some item else lookup tl key

(* Insere um elemento no começo da lista.
   Usado para extensão do ambiente, permitindo o shadowing das expressões. *)
let extend amb x item = (x, item) :: amb

(* Remove elementos repetidos de uma lista *)
let nub l =
  let ucons h t = if List.mem h t then t else h :: t in
  List.fold_right ucons l []

(* Calcula l1 - l2 (como sets) *)
let diff (l1 : 'a list) (l2 : 'a list) : 'a list =
  List.filter (fun a -> not (List.mem a l2)) l1

(* Tipos de L1 *)
type tipo =
  | TyInt
  | TyBool
  | TyFn of tipo * tipo
  | TyPair of tipo * tipo
  | TyEither of tipo * tipo
  | TyList of tipo
  | TyMaybe of tipo
  | TyVar of int (* Variáveis de tipo -- números *)

(* Impressao legível de monotipos  *)
let rec tipo_str (tp : tipo) : string =
  match tp with
  | TyInt ->
      "int"
  | TyBool ->
      "bool"
  | TyFn (t1, t2) ->
      "(" ^ tipo_str t1 ^ " -> " ^ tipo_str t2 ^ ")"
  | TyPair (t1, t2) ->
      "(" ^ tipo_str t1 ^ " * " ^ tipo_str t2 ^ ")"
  | TyEither (t1, t2) ->
      "either " ^ tipo_str t1 ^ " " ^ tipo_str t2
  | TyList t ->
      tipo_str t ^ " list"
  | TyMaybe t ->
      "maybe " ^ tipo_str t
  | TyVar n ->
      "X" ^ string_of_int n

(* Expressões de L1 sem anotações de tipo *)
type ident = string

type bop = Sum | Sub | Mult | Eq | Gt | Lt | Geq | Leq

type expr =
  | Num of int
  | Bool of bool
  | Var of ident
  | Binop of bop * expr * expr
  (* Pair related *)
  | Pair of expr * expr
  | Fst of expr
  | Snd of expr
  | If of expr * expr * expr
  (* Function related*)
  | Fn of ident * expr
  | App of expr * expr
  | Let of ident * expr * expr
  | LetRec of ident * ident * expr * expr
  | Pipe of expr * expr
  (* List related *)
  | Nil
  | Node of expr * expr
  | MatchList of expr * expr * ident * ident * expr
  (* Maybe related *)
  | Nothing
  | Just of expr
  | MatchMaybe of expr * expr * ident * expr
  (* Either related *)
  | Left of expr
  | Right of expr
  | MatchEither of expr * ident * expr * ident * expr

(* Impressão legível de expressão *)
let rec expr_str (e : expr) : string =
  match e with
  | Num n ->
      string_of_int n
  | Bool b ->
      string_of_bool b
  | Var x ->
      x
  | Binop (o, e1, e2) ->
      let s =
        match o with
        | Sum ->
            "+"
        | Sub ->
            "-"
        | Mult ->
            "*"
        | Leq ->
            "<="
        | Geq ->
            ">="
        | Eq ->
            "="
        | Lt ->
            "<"
        | Gt ->
            ">"
      in
      "(" ^ expr_str e1 ^ " " ^ s ^ " " ^ expr_str e2 ^ ")"
  (* Pair related *)
  | Pair (e1, e2) ->
      "(" ^ expr_str e1 ^ ", " ^ expr_str e2 ^ ")"
  | Fst e1 ->
      "fst " ^ expr_str e1
  | Snd e1 ->
      "snd " ^ expr_str e1
  | If (e1, e2, e3) ->
      "(if " ^ expr_str e1 ^ " then " ^ expr_str e2 ^ " else " ^ expr_str e3
      ^ ")"
  (* Function related *)
  | Fn (x, e1) ->
      "(fn " ^ x ^ " => " ^ expr_str e1 ^ ")"
  | App (e1, e2) ->
      "(" ^ expr_str e1 ^ " " ^ expr_str e2 ^ ")"
  | Let (x, e1, e2) ->
      "(let " ^ x ^ " = " ^ expr_str e1 ^ "\nin " ^ expr_str e2 ^ ")"
  | LetRec (f, x, e1, e2) ->
      "(let rec " ^ f ^ " = fn " ^ x ^ " => " ^ expr_str e1 ^ "\nin "
      ^ expr_str e2 ^ ")"
  | Pipe (e1, e2) ->
      expr_str e1 ^ " |> " ^ expr_str e2
  (* List related *)
  | Nil ->
      "Nil"
  | Node (e1, e2) ->
      expr_str e1 ^ " :: " ^ expr_str e2
  | MatchList (e1, e2, x, xs, e3) ->
      "match " ^ expr_str e1 ^ " with nil => " ^ expr_str e2 ^ "| " ^ x ^ " :: "
      ^ xs ^ " => " ^ expr_str e3
  (* Maybe related *)
  | Nothing ->
      "nothing"
  | Just e ->
      "Just " ^ expr_str e
  | MatchMaybe (e1, e2, x, e3) ->
      "match " ^ expr_str e1 ^ " with nothing => " ^ expr_str e2 ^ " | just "
      ^ x ^ " => " ^ expr_str e3
  (* Either related *)
  | Left e ->
      "left " ^ expr_str e
  | Right e ->
      "right " ^ expr_str e
  | MatchEither (e1, x, e2, y, e3) ->
      "match " ^ expr_str e1 ^ " with left " ^ x ^ " => " ^ expr_str e2
      ^ " | right " ^ y ^ " => " ^ expr_str e3

(* Código para geração de novas variáveis de tipo *)
let lastvar = ref 0

let newvar (_ : unit) : int =
  let x = !lastvar in
  lastvar := x + 1 ;
  x

(* Substituições de tipo
    int - Variável do tipo
    tipo - O tipo correspondente para substituir *)
type subst = (int * tipo) list

(* Imprime substituições *)
let rec print_subst (s : subst) =
  match s with
  | [] ->
      print_string "\n"
  | (a, b) :: t ->
      print_string ("X" ^ string_of_int a) ;
      print_string " |-> " ;
      print_string (tipo_str b) ;
      print_string "\n" ;
      print_subst t

(* Aplicação de substituição de tipos *)
let rec app_subs (s : subst) (tp : tipo) : tipo =
  match tp with
  | TyInt ->
      TyInt
  | TyBool ->
      TyBool
  | TyFn (t1, t2) ->
      TyFn (app_subs s t1, app_subs s t2)
  | TyPair (t1, t2) ->
      TyPair (app_subs s t1, app_subs s t2)
  | TyEither (t1, t2) ->
      TyEither (app_subs s t1, app_subs s t2)
  | TyList t ->
      TyList (app_subs s t)
  | TyMaybe t ->
      TyMaybe (app_subs s t)
  | TyVar x -> (
    (* Caso a variável não se encontre na lista de substituições, ela é mantida,
       do contrário, é substituída pelo tipo correspondente *)
    match lookup s x with None -> TyVar x | Some tp' -> tp' )

(* Equações de tipo.
    A lista
    [ (t1,t2) ; (u1,u2) ]
    representa o conjunto de equações de tipo
    { t1=t2, u1=u2 }
*)
type equacoes_tipo = (tipo * tipo) list

(* Imprime equações *)
let rec print_equacoes (c : equacoes_tipo) =
  match c with
  | [] ->
      print_string "\n"
  | (a, b) :: t ->
      print_string (tipo_str a) ;
      print_string " = " ;
      print_string (tipo_str b) ;
      print_string "\n" ;
      print_equacoes t

(* Aplicação de substituição a coleção de constraints.
   Dado as equações de tipo, aplica todas as substituições. *)
let app_constr (s : subst) (c : equacoes_tipo) : equacoes_tipo =
  List.map (fun (a, b) -> (app_subs s a, app_subs s b)) c

(* Composição de substituições: s1 o s2
   Equações com mesmo tipo são substituídos considerando-se as definições de s2. *)
let compose (s1 : subst) (s2 : subst) : subst =
  let r1 = List.map (fun (x, y) -> (x, app_subs s1 y)) s2 in
  let vs, _ = List.split s2 in
  let r2 = List.filter (fun (x, y) -> not (List.mem x vs)) s1 in
  r1 @ r2

(* Testa se variável de tipo (TyVar) ocorre no tipo dado *)
let rec var_in_tipo (v : int) (tp : tipo) : bool =
  match tp with
  | TyInt ->
      false
  | TyBool ->
      false
  | TyFn (t1, t2) ->
      var_in_tipo v t1 || var_in_tipo v t2
  | TyPair (t1, t2) ->
      var_in_tipo v t1 || var_in_tipo v t2
  | TyEither (t1, t2) ->
      var_in_tipo v t1 || var_in_tipo v t2
  | TyList t ->
      var_in_tipo v t
  | TyMaybe t ->
      var_in_tipo v t
  | TyVar x ->
      v = x

(* Uma tupla contendo uma lista de inteiros (variáveis de tipo) e um tipo (restritivo) associado *)
type politipo = int list * tipo

(* Free type variables em um tipo *)
let rec ftv (tp : tipo) : int list =
  match tp with
  | TyInt | TyBool ->
      []
  | TyFn (t1, t2) | TyPair (t1, t2) | TyEither (t1, t2) ->
      ftv t1 @ ftv t2
  | TyList t | TyMaybe t ->
      ftv t
  | TyVar n ->
      [n]

(* Ambientes de tipo - modificados para polimorfismo *)
type ty_env = (ident * politipo) list

let rec ftv_amb' (g : ty_env) : int list =
  match g with
  | [] ->
      []
  | (_, (vars, tp)) :: t ->
      diff (ftv tp) vars @ ftv_amb' t

(* Calcula todas as variáveis de tipo livres do ambiente de tipos *)
let ftv_amb (g : ty_env) : int list = nub (ftv_amb' g)

(* Cria novas variáveis para politipos quando estes são instanciados *)
let rec renamevars (pltp : politipo) : tipo =
  match pltp with
  | [], tp ->
      tp
  | h :: vars', tp ->
      let h' = newvar () in
      app_subs [(h, TyVar h')] (renamevars (vars', tp))

(* Unificação *)
exception UnifyFail of (tipo * tipo)

let rec unify (c : equacoes_tipo) : subst =
  match c with
  | [] ->
      []
  | (TyInt, TyInt) :: c' ->
      unify c'
  | (TyBool, TyBool) :: c' ->
      unify c'
  | (TyFn (x1, y1), TyFn (x2, y2)) :: c' ->
      unify ((x1, x2) :: (y1, y2) :: c')
  | (TyPair (x1, y1), TyPair (x2, y2)) :: c' ->
      unify ((x1, x2) :: (y1, y2) :: c')
  | (TyEither (x1, y1), TyEither (x2, y2)) :: c' ->
      unify ((x1, x2) :: (y1, y2) :: c')
  | (TyMaybe a, TyMaybe b) :: c' ->
      unify ((a, b) :: c')
  | (TyList a, TyList b) :: c' ->
      unify ((a, b) :: c')
  | (TyVar x1, TyVar x2) :: c' when x1 = x2 ->
      unify c'
  | (TyVar x1, tp2) :: c' ->
      if var_in_tipo x1 tp2 then raise (UnifyFail (TyVar x1, tp2))
      else compose (unify (app_constr [(x1, tp2)] c')) [(x1, tp2)]
  | (tp1, TyVar x2) :: c' ->
      if var_in_tipo x2 tp1 then raise (UnifyFail (tp1, TyVar x2))
      else compose (unify (app_constr [(x2, tp1)] c')) [(x2, tp1)]
  | (tp1, tp2) :: _' ->
      raise (UnifyFail (tp1, tp2))

(* Coleta *)
exception CollectFail of string

let rec collect (g : ty_env) (e : expr) : equacoes_tipo * tipo =
  match e with
  | Var x -> (
    match lookup g x with
    | None ->
        raise (CollectFail x)
    | Some pltp ->
        ([], renamevars pltp) (* Instancia poli *) )
  | Num n ->
      ([], TyInt)
  | Bool b ->
      ([], TyBool)
  | Binop (o, e1, e2) ->
      if List.mem o [Sum; Sub; Mult] then
        let c1, tp1 = collect g e1 in
        let c2, tp2 = collect g e2 in
        (c1 @ c2 @ [(tp1, TyInt); (tp2, TyInt)], TyInt)
      else
        let c1, tp1 = collect g e1 in
        let c2, tp2 = collect g e2 in
        (c1 @ c2 @ [(tp1, TyInt); (tp2, TyInt)], TyBool)
  (* Pair related *)
  | Pair (e1, e2) ->
      let c1, tp1 = collect g e1 in
      let c2, tp2 = collect g e2 in
      (c1 @ c2, TyPair (tp1, tp2))
  | Fst e1 ->
      let tA = newvar () in
      let tB = newvar () in
      let c1, tp1 = collect g e1 in
      (c1 @ [(tp1, TyPair (TyVar tA, TyVar tB))], TyVar tA)
  | Snd e1 ->
      let tA = newvar () in
      let tB = newvar () in
      let c1, tp1 = collect g e1 in
      (c1 @ [(tp1, TyPair (TyVar tA, TyVar tB))], TyVar tB)
  | If (e1, e2, e3) ->
      let c1, tp1 = collect g e1 in
      let c2, tp2 = collect g e2 in
      let c3, tp3 = collect g e3 in
      (c1 @ c2 @ c3 @ [(tp1, TyBool); (tp2, tp3)], tp2)
  (* Function related *)
  | Fn (x, e1) ->
      let tA = newvar () in
      let g' = (x, ([], TyVar tA)) :: g in
      let c1, tp1 = collect g' e1 in
      (c1, TyFn (TyVar tA, tp1))
  | App (e1, e2) ->
      let c1, tp1 = collect g e1 in
      let c2, tp2 = collect g e2 in
      let tA = newvar () in
      (c1 @ c2 @ [(tp1, TyFn (tp2, TyVar tA))], TyVar tA)
  | Let (x, e1, e2) ->
      let c1, tp1 = collect g e1 in
      let s1 = unify c1 in
      let tf1 = app_subs s1 tp1 in
      let polivars = nub (diff (ftv tf1) (ftv_amb g)) in
      let g' = (x, (polivars, tf1)) :: g in
      let c2, tp2 = collect g' e2 in
      (c1 @ c2, tp2)
  | LetRec (f, x, e1, e2) ->
      let tA = newvar () in
      let tB = newvar () in
      let g2 = (f, ([], TyFn (TyVar tA, TyVar tB))) :: g in
      let g1 = (x, ([], TyVar tA)) :: g2 in
      let c1, tp1 = collect g1 e1 in
      let s1 = unify (c1 @ [(tp1, TyVar tB)]) in
      let tf1 = app_subs s1 (TyFn (TyVar tA, TyVar tB)) in
      let polivars = nub (diff (ftv tf1) (ftv_amb g)) in
      let g' = (f, (polivars, tf1)) :: g in
      let c2, tp2 = collect g' e2 in
      (c1 @ [(tp1, TyVar tB)] @ c2, tp2)
  | Pipe (e1, e2) ->
      let c1, tp1 = collect g e1 in
      let c2, tp2 = collect g e2 in
      let tA = newvar () in
      (c1 @ c2 @ [(tp2, TyFn (tp1, TyVar tA))], TyVar tA)
  (* List related *)
  | Nil ->
      ([], TyList (TyVar (newvar ())))
  | Node (e1, e2) ->
      let c1, tp1 = collect g e1 in
      let c2, tp2 = collect g e2 in
      (c1 @ c2 @ [(tp2, TyList tp1)], tp2)
  | MatchList (e1, e2, x, xs, e3) ->
      let c1, tp1 = collect g e1 in
      let c2, tp2 = collect g e2 in
      let xNew = TyVar (newvar ()) in
      let g' = (x, ([], xNew)) :: (xs, ([], tp1)) :: g in
      let c3, tp3 = collect g' e3 in
      (c1 @ c2 @ c3 @ [(tp1, TyList xNew); (tp2, tp3)], tp2)
  (* Maybe related *)
  | Nothing ->
      ([], TyMaybe (TyVar (newvar ())))
  | Just e ->
      let c1, tp1 = collect g e in
      (c1, TyMaybe tp1)
  | MatchMaybe (e1, e2, x, e3) ->
      let c1, tp1 = collect g e1 in
      let c2, tp2 = collect g e2 in
      let xNew = TyVar (newvar ()) in
      let g' = (x, ([], xNew)) :: g in
      let c3, tp3 = collect g' e3 in
      (c1 @ c2 @ c3 @ [(tp1, TyMaybe xNew); (tp2, tp3)], tp2)
  (* Either related*)
  | Left e ->
      let c, tp = collect g e in
      let xNew = TyVar (newvar ()) in
      (c, TyEither (tp, xNew))
  | Right e ->
      let c, tp = collect g e in
      let xNew = TyVar (newvar ()) in
      (c, TyEither (xNew, tp))
  | MatchEither (e1, x, e2, y, e3) ->
      let c1, tp1 = collect g e1 in
      let xNew = TyVar (newvar ()) in
      let yNew = TyVar (newvar ()) in
      let gx = (x, ([], xNew)) :: g in
      let c2, tp2 = collect gx e2 in
      let gy = (y, ([], yNew)) :: g in
      let c3, tp3 = collect gy e3 in
      (c1 @ c2 @ c3 @ [(tp1, TyEither (xNew, yNew)); (tp2, tp3)], tp2)

(* INFERÊNCIA DE TIPOS - CHAMADA PRINCIPAL *)
let type_infer (e : expr) : bool =
  print_string "\nExpressão:\n" ;
  print_string (expr_str e) ;
  print_string "\n\n" ;
  try
    let c, tp = collect [] e in
    print_string "\nEquações de tipo coletadas:\n" ;
    print_equacoes c ;
    let s = unify c in
    let tf = app_subs s tp in
    print_string "Tipo inferido: " ;
    print_string (tipo_str tp) ;
    print_string "\n\nSubstituição produzida por unify:\n" ;
    print_subst s ;
    print_string "Tipo inferido (após subs): " ;
    print_string (tipo_str tf) ;
    print_string "\n\n" ;
    true
  with
  | CollectFail x ->
      print_string "Erro: variável " ;
      print_string x ;
      print_string "não declarada!\n\n" ;
      false
  | UnifyFail (tp1, tp2) ->
      print_string "Erro: impossível unificar os tipos\n* " ;
      print_string (tipo_str tp1) ;
      print_string "\n* " ;
      print_string (tipo_str tp2) ;
      print_string "\n\n" ;
      false

(*===============================================*)

type valor =
  | VNum of int
  | VBool of bool
  | VPair of valor * valor
  | VClos of ident * expr * renv
  | VRclos of ident * ident * expr * renv
  | VNil
  | VNothing
  | VJust of valor
  | VLeft of valor
  | VRight of valor
  | VList of valor * valor

and renv = (ident * valor) list

exception BugTypeInfer

exception DivZero

let compute (oper : bop) (v1 : valor) (v2 : valor) : valor =
  match (oper, v1, v2) with
  | Sum, VNum n1, VNum n2 ->
      VNum (n1 + n2)
  | Sub, VNum n1, VNum n2 ->
      VNum (n1 - n2)
  | Mult, VNum n1, VNum n2 ->
      VNum (n1 * n2)
  | Eq, VNum n1, VNum n2 ->
      VBool (n1 = n2)
  | Gt, VNum n1, VNum n2 ->
      VBool (n1 > n2)
  | Lt, VNum n1, VNum n2 ->
      VBool (n1 < n2)
  | Geq, VNum n1, VNum n2 ->
      VBool (n1 >= n2)
  | Leq, VNum n1, VNum n2 ->
      VBool (n1 <= n2)
  | _ ->
      raise BugTypeInfer

let rec eval (renv : renv) (e : expr) : valor =
  match e with
  | Num n ->
      VNum n
  | Bool b ->
      VBool b
  | Var x -> (
    match lookup renv x with None -> raise BugTypeInfer | Some v -> v )
  | Binop (oper, e1, e2) ->
      let v1 = eval renv e1 in
      let v2 = eval renv e2 in
      compute oper v1 v2
  | Pair (e1, e2) ->
      let v1 = eval renv e1 in
      let v2 = eval renv e2 in
      VPair (v1, v2)
  | Fst e -> (
    match eval renv e with VPair (v1, _) -> v1 | _ -> raise BugTypeInfer )
  | Snd e -> (
    match eval renv e with VPair (_, v2) -> v2 | _ -> raise BugTypeInfer )
  | If (e1, e2, e3) -> (
    match eval renv e1 with
    | VBool true ->
        eval renv e2
    | VBool false ->
        eval renv e3
    | _ ->
        raise BugTypeInfer )
  | Fn (x, e1) ->
      VClos (x, e1, renv)
  | App (e1, e2) -> (
      let v1 = eval renv e1 in
      let v2 = eval renv e2 in
      match v1 with
      | VClos (x, ebdy, renv') ->
          let renv'' = extend renv' x v2 in
          eval renv'' ebdy
      | VRclos (f, x, ebdy, renv') ->
          let renv'' = extend renv' x v2 in
          let renv''' = extend renv'' f v1 in
          eval renv''' ebdy
      | _ ->
          raise BugTypeInfer )
  | Let (x, e1, e2) ->
      let v1 = eval renv e1 in
      eval (extend renv x v1) e2
  | LetRec (f, x, e1, e2) ->
      let renv' = extend renv f (VRclos (f, x, e1, renv)) in
      eval renv' e2
  | Pipe (e1, e2) -> (
      let v1 = eval renv e1 in
      let close = eval renv e2 in
      match close with
      | VClos (x, ebdy, renv') ->
          let renv'' = extend renv' x v1 in
          eval renv'' ebdy
      | VRclos (f, x, ebdy, renv') ->
          let renv'' = extend renv' x v1 in
          let renv''' = extend renv'' f close in
          eval renv''' ebdy
      | _ ->
          raise BugTypeInfer )
  | Nil ->
      VNil
  | Node (e1, e2) ->
      let v1 = eval renv e1 in
      let v2 = eval renv e2 in
      VList (v1, v2)
  | MatchList (e1, e2, x, xs, e3) -> (
      let v1 = eval renv e1 in
      match v1 with
      | VNil ->
          eval renv e2
      | VList (v, vs) ->
          eval (extend (extend renv x v) xs vs) e3
      | _ ->
          raise BugTypeInfer )
  | Nothing ->
      VNothing
  | Just e ->
      let v1 = eval renv e in
      VJust v1
  | MatchMaybe (e1, e2, x, e3) -> (
      let v1 = eval renv e1 in
      match v1 with
      | VNothing ->
          eval renv e2
      | VJust v ->
          eval (extend renv x v) e3
      | _ ->
          raise BugTypeInfer )
  | Left e ->
      VLeft (eval renv e)
  | Right e ->
      VRight (eval renv e)
  | MatchEither (e1, x, e2, y, e3) -> (
      let v1 = eval renv e1 in
      match v1 with
      | VLeft v ->
          eval (extend renv x v) e2
      | VRight v ->
          eval (extend renv y v) e3
      | _ ->
          raise BugTypeInfer )

exception ExecFail

let check_type (e : expr) : bool =
  try
    let c, tp = collect [] e in
    let s = unify c in
    let _ = app_subs s tp in
    true
  with
  | CollectFail _ ->
      false
  | UnifyFail _ ->
      false

(* Test aux function *)
let exec (e : expr) : valor =
  match check_type e with true -> eval [] e | false -> raise ExecFail
