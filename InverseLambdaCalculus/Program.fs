open System

// F# の詳細については、http://fsharp.org を参照してください
// 詳細については、'F# チュートリアル' プロジェクトを参照してください。

[<StructuredFormatDisplay("{AsString}")>]
type Term =
    | Var of string
    | Lam of string * Term
    | App of Term * Term
with
    member this.isValue =
        match this with
        | Var _ | Lam _ -> true
        | App _ -> false
    member this.AsString =
        match this with
        | Var v -> v
        | Lam (v, t) -> sprintf "\\%s. %A" v t
        | App (f, x) -> sprintf "(%A %A)" f x
    member this.freeVariable = 
        match this with
        | Var v -> Set.singleton v
        | Lam (v, t) -> t.freeVariable - Set.singleton v
        | App (f, x) -> f.freeVariable + x.freeVariable
    member this.Substitute v t =
        match this with
        | Var v' when v = v' -> t
        | Var _ -> this
        | Lam (v', t') -> Lam (v', t'.Substitute v t)
        | App (f, x) -> App (f.Substitute v t, x.Substitute v t)

let is_value (t: Term): bool = t.isValue

type State = Term list * Term

let rec make_hole (term: Term) (v: string): Term =
    match term with
    | Var v' when v = v' -> term
    | Var _ -> Var "_"
    | Lam (_, t) -> Lam ("_", make_hole t v)
    | App (f, x) -> App (make_hole f v, make_hole x v)

let rec beta (state: State): State =
    let (history, term) = state
    match term with
    | App (f, x) when not f.isValue ->
        let (history, f) = beta (history, f)
        match history with
        | head :: history -> App (head, Var "_") :: history, App (f, x)
        | _ -> failwith "internal beta must push a history"
    | App (f, x) when not x.isValue ->
        let (history, x) = beta (history, x)
        match history with
        | head :: histroy -> App (Var "_", head) :: history, App (f, x)
        | _ -> failwith "internal beta must push a history"
    | App (Lam (x, t), v) -> 
        if t.freeVariable.Contains x then
            App (Lam (x, make_hole t x), Var "_") :: history, t.Substitute x v
        else
            App (Lam (x, Var "_"), v) :: history, t
    | _ -> failwith "cannot perform beta reduction"

let rec inv_beta (state: State): State = 
    let rec inv_subst x holed t =
        match holed, t with
        | Var x', _ when x = x' -> Some t, Var x
        | Var "_", _ -> (None, t)
        | Lam ("_", holed), Lam (x', t) -> 
            let (arg, t) = inv_subst x holed t
            arg, Lam (x', t)
        | App (f, t), App (f', t') -> 
            let (argl, tl) = inv_subst x f f'
            let (argr, tr) = inv_subst x t t'
            match argl, argr with
            | Some l, Some r when l = r -> Some l, App (tl, tr)
            | Some _, Some _ -> failwith "same variable reduced to different value"
            | Some arg, None | None, Some arg -> Some arg, App (tl, tr)
            | None, None -> None, App (tl, tr)
        | _ -> failwith "invalid hole"
    let (history, term) = state
    match history with
    | head :: history ->
        match head with
        | App (Lam (x, Var "_"), v) -> history, (App (Lam (x, term), v))
        | App (Lam (x, holed), Var "_") -> 
            match inv_subst x holed term with
            | Some arg, t -> history, App (Lam (x, t), arg)
            | None, _ -> failwith "cannot find argument"
        | App (head, Var "_") -> 
            match term with
            | App (f, x) -> history, App (inv_beta ([head], f) |> snd, x)
            | _ -> failwith "cannot inverse beta reduction"
        | App (Var "_", head) ->
            match term with
            | App (f, x) -> history, App (f, inv_beta ([head], f) |> snd)
            | _ -> failwith "cannot inverse beta reduction"
        | _ -> failwith "cannot inverse beta reduction"
    | _ -> failwith "no history"

let reduce_and_inv term =
    let status = ref ([], term)
    printfn "%A" !status
    while !status |> snd |> is_value |> not do
        status := beta !status
        printfn "%A" !status
    while !status |> fst |> (fun h -> List.length h > 0) do
        status := inv_beta !status
        printfn "%A" !status

[<EntryPoint>]
let main argv = 
    let apply = Lam ("f", Lam ("x", App (Var "f", Var "x")))
    let id = Lam ("y", Var "y")
    let hoge = Var "z"
    reduce_and_inv (App (App (apply, id), hoge))

    let true_ = Lam ("tt", Lam ("ft", Var "tt"))
    let false_ = Lam ("tf", Lam ("ff", Var "ff"))
    let cond = Lam ("cond", Lam ("tv", Lam ("fv", App (App (Var "cond", Var "tv"), Var "fv"))))

    let zero = Lam ("f0", Lam ("z0", Var "z0"))
    let one = Lam ("f1", Lam ("z1", App (Var "f1", Var "z0")))
    let two = Lam ("f2", Lam ("z2", App (Var "f2", App (Var "f2", Var "z2"))))
    let succ = Lam ("nsucc", Lam ("fsucc", Lam ("nsucc", App (Var "fsucc", App (App (Var "nsucc", Var "fsucc"), Var "zsucc")))))
    let iszero = Lam ("nis0", App (App (Var "nis0", Lam ("xis0", true_)), false_))
    let add = Lam ("nadd", Lam ("madd", Lam ("fadd", Lam ("zadd", App (App (Var "nadd", (App (Var "madd", Var "fadd"))), Var "zadd")))))

    reduce_and_inv (App (App (add, one), two))

    0 // 整数の終了コードを返します
