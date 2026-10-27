module

public import Certificates.Data.CFSGNative.Co1Schreier.Base

public section

namespace CFSG.Sporadic.Co1Patterson.Native

open CFSG.Sporadic.Co1Schreier.Native

@[expose] def colOf (N : Rows) (j : Nat) : Nat :=
  (List.range 24).foldl (fun acc i => if (N[i]?.getD 0).testBit j then acc ||| (1 <<< i) else acc)
    0

@[expose] def reduceAgainst (B : List (Nat × Nat)) (p : Nat × Nat) : Nat × Nat :=
  B.foldl (fun q b => if q.1.testBit b.1.log2 then (q.1 ^^^ b.1, q.2 ^^^ b.2) else q) p

@[expose] def insertSorted : List (Nat × Nat) → Nat × Nat → List (Nat × Nat)
  | [], p => [p]
  | q :: t, p => if p.1.log2 < q.1.log2 then q :: insertSorted t p else p :: q :: t

@[expose] def elimStep (st : List (Nat × Nat) × List Nat) (p : Nat × Nat) :
    List (Nat × Nat) × List Nat :=
  let r := reduceAgainst st.1 p
  if r.1 == 0 then (st.1, st.2 ++ [r.2]) else (insertSorted st.1 r, st.2)

@[expose] def kerIm (N : Rows) : List (Nat × Nat) × List Nat :=
  (List.range 24).foldl (fun st j => elimStep st (colOf N j, 1 <<< j)) ([], [])

@[expose] def echelonize (L : List Nat) : List Nat :=
  (L.foldl (fun B v =>
    let r := reduceAgainst B (v, 0)
    if r.1 == 0 then B else insertSorted B r) []).map Prod.fst

@[expose] def echelonOK : List Nat → Bool
  | [] => true
  | [v] => decide (0 < v) && decide (v < 2 ^ 24)
  | v :: w :: t => decide (0 < v) && decide (v < 2 ^ 24) && decide (w.log2 < v.log2) &&
      echelonOK (w :: t)

@[expose] def fixDimIs (M : Rows) (d : Nat) : Bool :=
  let N := add M one
  let ki := kerIm N
  let K := echelonize ki.2
  K.length == d && ki.1.length + d == 24 && K.all (fun v => act N v == 0) && echelonOK K &&
    ki.1.all (fun p => decide (p.2 < 2 ^ 24) && act N p.2 == p.1) &&
    echelonOK (ki.1.map Prod.fst)

@[expose] def fixDim (M : Rows) : Nat := (echelonize (kerIm (add M one)).2).length

end CFSG.Sporadic.Co1Patterson.Native
