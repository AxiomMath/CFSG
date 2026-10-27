module

public import Certificates.Data.SmithL6Check
public import Certificates.Data.SmithECheck

public section

namespace CFSG.SmithL6

open CFSG.SmithE (applyCols SpanData spanData gensOf)

@[expose] def mfIsWt (v : Nat) : Bool := let j := wtIdx[v]!; decide (j < 1395) && wtArr[j]! == v

@[expose] def mfChkWt : Bool :=
  (List.range 1395).all (fun j => wtIdx[wtArr[j]!]! == j) &&
  (List.range 1395).all (fun i => decide (wtArr[i]! < 2 ^ 20) && wtArr[i]! != 0 &&
    (List.range 1395).any (fun j => adjM i j && wtArr[j]! != wtArr[i]!) &&
    (List.range 1395).all (fun j => adjM i j || !mfIsWt (wtArr[i]! ^^^ wtArr[j]!)))

@[expose] def mfChkTvAdj : Bool :=
  (List.range 1953).all fun k => (List.range 1395).all fun i =>
    let j := planeImg k i
    decide (j < 1395) && adjM i j

@[expose] def mfPairKind (k l : Nat) : Nat :=
  let p := tvPair k
  let q := tvPair l
  let a := form p.2 q.1
  let b := form q.2 p.1
  if a == b then (if a then 1 else 0) else 2

@[expose] def mfCommuteB (A B : Array Nat) : Bool :=
  (List.range 20).all fun m => applyCols A B[m]! == applyCols B A[m]!

@[expose] def mfBraidB (A B : Array Nat) : Bool :=
  (List.range 20).all fun m => applyCols A (applyCols B A[m]!) == applyCols B (applyCols A B[m]!)

@[expose] def mfDihB (A B : Array Nat) : Bool :=
  (List.range 20).all fun m =>
    applyCols A (applyCols B (applyCols A B[m]!)) == applyCols B (applyCols A (applyCols B A[m]!))

@[expose] def mfChkPair0 : Bool :=
  (List.range 1953).all fun l =>
    match mfPairKind 0 l with
    | 0 => mfCommuteB tvArr[0]! tvArr[l]!
    | 1 => mfBraidB tvArr[0]! tvArr[l]!
    | _ => mfDihB tvArr[0]! tvArr[l]!

@[expose] def mfSpanArr : Array SpanData := tvArr.map spanData

@[expose] def mfChkSpan : Bool :=
  (List.range 1953).all fun k => let D := mfSpanArr[k]!; let g := gensOf tvArr[k]!
    D.basis.size == 6 && D.coef.size == 20 &&
    (List.range 20).all fun m => decide (D.coef[m]! < 64) &&
      applyCols D.basis D.coef[m]! == g[m]! && applyCols D.syn g[m]! == 0

@[expose] def mfChkInt0 : Bool :=
  let D0 := mfSpanArr[0]!
  (List.range 1953).all fun l => decide (l = 0) ||
    (let S := D0.basis.map (applyCols mfSpanArr[l]!.syn)
     let h0 := mfPairKind 0 l == 0
     (List.range 64).all fun d => applyCols S d != 0 ||
       (let v := applyCols D0.basis d; v == 0 || (h0 && mfIsWt v)))

@[expose] def e4fApplyWord : List Nat → Nat → Nat
  | [], c => c
  | r :: w, c => applyCols (tvCols r) (e4fApplyWord w c)

end CFSG.SmithL6
