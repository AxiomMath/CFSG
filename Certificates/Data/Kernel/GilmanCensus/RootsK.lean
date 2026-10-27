module

public import Certificates.Data.Kernel.GilmanCensus.Twin

public section

namespace Certificates.GilmanCensusK

@[expose] def cartanK (isF : Bool) (n : Nat) : List (List Int) :=
  let base : List (List Int) :=
    (List.range n).map fun i => (List.range n).map fun j => if i == j then 2 else 0
  let edges : List (Nat × Nat) :=
    if isF then [(0, 1), (1, 2), (2, 3)]
    else [(0, 2), (2, 3), (3, 4), (4, 5), (1, 3)] ++ (if n ≥ 7 then [(5, 6)] else []) ++
      (if n ≥ 8 then [(6, 7)] else [])
  let A := edges.foldl (fun A e =>
    let A := A.set e.1 ((A.getD e.1 []).set e.2 (-1))
    A.set e.2 ((A.getD e.2 []).set e.1 (-1))) base
  if isF then A.set 1 ((A.getD 1 []).set 2 (-2)) else A

@[expose] def simpleK (n : Nat) : List (List Int) :=
  (List.range n).map fun i => (List.range n).map fun j => if i == j then 1 else 0

@[expose] def colSumK (A : List (List Int)) (n : Nat) (r : List Int) (i : Nat) : Int :=
  (List.range' 0 n).foldl (fun c j => c + r.getD j 0 * (A.getD j []).getD i 0) 0

@[expose] def grStep (A : List (List Int)) (n : Nat) (r : List Int)
    (st : List (List Int) × List (List Int)) (i : Nat) : List (List Int) × List (List Int) :=
  let s := r.set i (r.getD i 0 - colSumK A n r i)
  if (s.all (fun x => decide (x ≥ 0)) && !st.2.contains s) = true then (st.1 ++ [s], st.2 ++ [s])
  else st

@[expose] def grGo (A : List (List Int)) (n : Nat) :
    Nat → List (List Int) → List (List Int) → Option (List (List Int))
  | 0, _, _ => none
  | f + 1, todo, all =>
    match todo.getLast? with
    | none => some all
    | some r =>
      let st := (List.range' 0 n).foldl (grStep A n r) (todo.dropLast, all)
      grGo A n f st.1 st.2

@[expose] def rankOf (m : Nat) : Nat := if (m == 0) = true then 4 else if m == 4 then 7 else if m == 5 then 8 else 6

@[expose] def rootsOkK (m : Nat) (AR : List (List Nat)) : Bool :=
  grGo (cartanK (m == 0) (rankOf m)) (rankOf m) 200 (simpleK (rankOf m)) (simpleK (rankOf m)) ==
    some (toI AR)

end Certificates.GilmanCensusK

end
