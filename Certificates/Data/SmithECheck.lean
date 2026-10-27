module

public import Certificates.Data.SmithEModel

public section

namespace CFSG.SmithE

open CFSG.F4.Native

@[expose] def wtArr : Array Nat := Array.ofFn (n := 891) fun i => wt i.val

@[expose] def maskArr : Array Nat := Array.ofFn (n := 891) fun i => wMask i.val

@[expose] def wtIdx : Array Nat :=
  (List.range 891).foldl (fun A j => A.set! wtArr[j]! j) (Array.replicate (2 ^ 20) 891)

@[expose] def isWt (v : Nat) : Bool := let j := wtIdx[v]!; decide (j < 891) && wtArr[j]! == v

@[expose] def adjM (i j : Nat) : Bool := atLeast 16 (maskArr[i]! &&& maskArr[j]!)

@[expose] def modelOK (i : Nat) : Bool :=
  let W := wB i
  hermC W.1 W.1 == 0 && hermC W.2.1 W.2.1 == 0 && hermC W.2.2 W.2.2 == 0 &&
    hermC W.1 W.2.1 == 0 && hermC W.1 W.2.2 == 0 && hermC W.2.1 W.2.2 == 0 &&
    atLeast 64 (wMask i) && !atLeast 65 (wMask i) && wedgeScalar W != 0 &&
    (List.range 10).all fun k =>
      f4sq (f4mul (wedgeScalar W) (pluck W k)) == f4mul (wedgeScalar W) (pluck W (19 - k))

@[expose] def chkW : Bool :=
  (List.range 891).all (fun j => wtIdx[wtArr[j]!]! == j) &&
  (List.range 891).all modelOK &&
  (List.range 891).all (fun i => wtArr[i]! != 0 &&
    (List.range 891).any (fun j => adjM i j && wtArr[j]! != wtArr[i]!) &&
    (List.range 891).all (fun j => adjM i j || !isWt (wtArr[i]! ^^^ wtArr[j]!)))

@[expose] def tvArr : Array (Array Nat) := Array.ofFn (n := 693) fun k => tvCols k.val

@[expose] def chkT : Bool :=
  (List.range 693).all fun k => let T := tvArr[k]!
    (List.range 891).all fun i => let v := applyCols T wtArr[i]!; let j := wtIdx[v]!
      decide (j < 891) && wtArr[j]! == v && adjM i j

@[expose] def commuteB (A B : Array Nat) : Bool :=
  (List.range 20).all fun m => applyCols A B[m]! == applyCols B A[m]!

@[expose] def braidB (A B : Array Nat) : Bool :=
  (List.range 20).all fun m => applyCols A (applyCols B A[m]!) == applyCols B (applyCols A B[m]!)

@[expose] def chkP : Bool :=
  (List.range 693).all fun k => (List.range 693).all fun l => decide (l ≤ k) ||
    (if hermC uPts[k]! uPts[l]! == 0 then commuteB tvArr[k]! tvArr[l]!
      else braidB tvArr[k]! tvArr[l]!)

@[expose] def lowBit (r : Nat) : Nat := Nat.log2 (r &&& (r ^^^ (r - 1)))

@[expose] def reduceBy (E : List (Nat × Nat)) (v : Nat) : Nat :=
  E.foldl (fun v be => if v.testBit be.1 then v ^^^ be.2 else v) v

@[expose] def insertVec (E : List (Nat × Nat)) (g : Nat) : List (Nat × Nat) :=
  let r := reduceBy E g
  if r == 0 then E else
    let b := lowBit r
    (E.map fun be => if be.2.testBit b then (be.1, be.2 ^^^ r) else be) ++ [(b, r)]

@[expose] def gensOf (T : Array Nat) : Array Nat :=
  Array.ofFn (n := 20) fun m => T[m.val]! ^^^ 2 ^ m.val

@[expose] def echelon (T : Array Nat) : List (Nat × Nat) := (gensOf T).toList.foldl insertVec []

structure SpanData where
  basis : Array Nat
  coef : Array Nat
  syn : Array Nat
deriving Inhabited

@[expose] def spanData (T : Array Nat) : SpanData :=
  let E := echelon T
  { basis := (E.map (·.2)).toArray
    coef := (gensOf T).map fun v => (List.range E.length).foldl
      (fun acc i => if v.testBit (E[i]!).1 then acc + 2 ^ i else acc) 0
    syn := Array.ofFn (n := 20) fun m => reduceBy E (2 ^ m.val) }

@[expose] def spanArr : Array SpanData := tvArr.map spanData

@[expose] def chkSpan : Bool :=
  (List.range 693).all fun k => let D := spanArr[k]!; let g := gensOf tvArr[k]!
    D.basis.size == 6 && D.coef.size == 20 &&
    (List.range 20).all fun m => decide (D.coef[m]! < 64) &&
      applyCols D.basis D.coef[m]! == g[m]! && applyCols D.syn g[m]! == 0

@[expose] def chkI : Bool :=
  (List.range 693).all fun k => let Dk := spanArr[k]!
    (List.range 693).all fun l => decide (l ≤ k) ||
      (let S := Dk.basis.map (applyCols spanArr[l]!.syn)
       let h0 := hermC uPts[k]! uPts[l]! == 0
       (List.range 64).all fun d => applyCols S d != 0 ||
         (let v := applyCols Dk.basis d; v == 0 || (h0 && isWt v)))

end CFSG.SmithE
