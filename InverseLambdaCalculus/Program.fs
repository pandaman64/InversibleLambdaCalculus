open System

// F# の詳細については、http://fsharp.org を参照してください
// 詳細については、'F# チュートリアル' プロジェクトを参照してください。

[<StructuredFormatDisplayAttribute("{AsString}")>]
type Var =
    | Bound of int
    | Unbound of string
with
    member this.AsString = 
        match this with
        | Bound i -> sprintf "%d" i
        | Unbound x -> x

[<StructuredFormatDisplay("{AsString}")>]
type Term =
    | Var of Var
    | Lam of Term
    | App of Term * Term
with
    member this.isValue =
        match this with
        | Var _ | Lam _ -> true
        | App _ -> false
    member this.AsString =
        match this with
        | Var x -> sprintf "%A" x
        | Lam t -> sprintf "\\.%A" t
        | App (t, t') -> sprintf "(%A %A)" t t'

let is_value (t: Term): bool = t.isValue

let rec shift (level: int) (lower_bound: int) (t: Term): Term =
    match t with
    | Var (Bound j) when j >= lower_bound -> Var (Bound (j + level))
    | Var _ -> t
    | Lam t -> Lam (shift level (lower_bound + 1) t)
    | App (t, t') -> App (shift level lower_bound t, shift level lower_bound t')

[<StructuredFormatDisplayAttribute("{AsString}")>]
type SubstPos =
    | Here
    | Down of SubstPos
    | Left of SubstPos
    | Right of SubstPos
with
    member this.AsString =
        match this with
        | Here -> "o"
        | Down p -> sprintf "\\.%A" p
        | Left p -> sprintf "(%A _)" p
        | Right p -> sprintf  "(_ %A)" p

let rec substitute (i: int) (v: Term) (t: Term): SubstPos list * Term =
    match t with
    | Var (Bound j) when i = j -> [Here], v
    | Var _ -> [], t
    | Lam t -> 
        let pos, t = substitute (i + 1) (shift 1 0 v) t
        List.map Down pos, Lam t
    | App (t, t') -> 
        let pos, t = substitute i v t
        let pos', t' = substitute i v t'
        List.append (List.map Left pos) (List.map Right pos'), App (t, t')

[<StructuredFormatDisplayAttribute("{AsString}")>]
type Transition =
    | AppLeft of Transition
    | AppRight of Transition
    | ApplySubst of SubstPos list * Term
    | Lambda of Transition
with
    member this.AsString = 
        match this with
        | AppLeft t -> sprintf "(%A _)" t
        | AppRight t -> sprintf "(_ %A)" t
        | ApplySubst (pos, t) -> sprintf "(\\.%A %A)" pos t
        | Lambda t -> sprintf "\\.%A" t

let rec tryBeta (term: Term): (Transition * Term) option =
    match term with 
    | App (Lam t, v) when v.isValue ->
        let pos, t = substitute 0 (shift 1 0 v) t
        Some (ApplySubst (pos, v), shift -1 0 t)
    | App (t, t') ->
        match tryBeta t with
        | Some (tran, t) -> Some (AppLeft tran, App (t, t'))
        | None ->
            match tryBeta t' with
            | Some (tran, t') -> Some (AppRight tran, App (t, t'))
            | None -> None
    | Lam t ->
        match tryBeta t with
        | Some (tran, t) -> Some (Lambda tran, Lam t)
        | None -> None
    | _ -> None

let rec inv_beta (tran: Transition) (term: Term): Term =
    let rec inv_subst pos i t =
        match pos with
        | Here -> Var (Bound i)
        | Down pos -> 
            match t with
            | Lam t -> inv_subst pos (i + 1) t |> Lam
            | _ -> failwith "invalid position"
        | Left pos ->
            match t with
            | App (t, t') -> App (inv_subst pos i t, t')
            | _ -> failwith "invalid position"
        | Right pos ->
            match t with
            | App (t, t') -> App (t, inv_subst pos i t')
            | _ -> failwith "invalid position"
    match tran with
    | AppLeft tran -> 
        match term with
        | App (t, t') -> App (inv_beta tran t, t')
        | _ -> failwith "invalid transition"
    | AppRight tran ->
        match term with
        | App (t, t') -> App (t,inv_beta tran t')
        | _ -> failwith "invalid transition"
    | ApplySubst (pos, t) -> App (List.fold (fun term pos -> inv_subst pos 0 term) term pos |> Lam, t)
    | Lambda tran ->
        match term with
        | Lam t -> Lam (inv_beta tran t)
        | _ -> failwith "invalid transition"

let reduce_and_inv (term: Term) =
    let mutable history = []
    let mutable term = term
    printfn "%A %A" history term

    let rec loop () =
        match tryBeta term with
        | Some (tran, t) ->
            history <- tran :: history
            term <- t
            printfn "%A %A" history term
            loop()
        | None -> ()

    loop ()

    while List.length history > 0 do
        term <- inv_beta history.Head term
        history <- history.Tail
        printfn "%A %A" history term

[<EntryPoint>]
let main argv = 
    let apply = Lam (Lam (App (Var (Bound 1), Var (Bound 0))))
    let id = Lam (Var (Bound 0))
    let hoge = Var (Unbound "hoge")
    reduce_and_inv (App (App (apply, id), hoge))

    printfn ""

    let zero = Lam (Lam (Var (Bound 0)))
    let one = Lam (Lam (App (Var (Bound 1), Var (Bound 0))))
    let succ = Lam (Lam (Lam (App (Var (Bound 1), App (App (Var (Bound 2), Var (Bound 1)), Var (Bound 0))))))
    reduce_and_inv (App (succ, zero))

    0 // 整数の終了コードを返します
