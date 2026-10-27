module

public import Certificates.Data.GMS78RuB1Data
public import CFSG.Sporadic.Schreier.RuCheckCentersInputs
public import CFSG.Sporadic.Schreier.RuCheckInvInputs
public meta import CFSG.Sporadic.Schreier.RuCheckCentersInputs
public meta import CFSG.Sporadic.Schreier.RuCheckInvInputs

public section

namespace CFSG.Sporadic.RuSchreier.RuB1

open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.Sporadic.RuSchreier

@[expose] def pickBy {α : Type} (r : α → α → Bool) : List α → List α
  | [] => []
  | a :: l => let p := pickBy r l; if p.any (r a) then p else a :: p

@[expose] def xArr (j : Nat) : Array Nat :=
  compA 4060 (compA 4060 (powA 4060 ruC0A (j / 7)) ruEArr[j % 7]!)
    (powA 4060 (ruInv ruC0A) (j / 7))

@[expose] def xList : Array (Array Nat) := Array.ofFn (n := 35) fun j => xArr j.val

@[expose] def g5A : Array Nat := powA 4060 ruC0A 4

@[expose] def xKept (j : Nat) : Bool := decide (j < 7) || j % 7 != 0

@[expose] def xCheckWith (xs : Array (Array Nat)) : Bool :=
  (allLt 35 fun j => allLt 35 fun j' =>
    let p := compA 4060 xs[j]! xs[j']!
    eqA 4060 p (idA 4060) || Nat.any 35 fun j'' _ => eqA 4060 p xs[j'']!) &&
  (allLt 35 fun j => allLt 35 fun j' =>
    eqA 4060 (compA 4060 xs[j]! xs[j']!) (compA 4060 xs[j']! xs[j]!)) &&
  (allLt 35 fun j => eqA 4060 (compA 4060 xs[j]! xs[j]!) (idA 4060)) &&
  (allLt 35 fun j => siftA 4060 ruLevS (ruBaseArr 4060 ruS4060ChainBase) 0 xs[j]!) &&
  (allLt 35 fun j => allLt 2 fun g => Nat.any 35 fun j' _ =>
    eqA 4060 (ruConjA #[ruC0A, ruC1A][g]! xs[j]!) xs[j']!) &&
  (allLt 35 fun j => allLt 35 fun j' =>
    !(xKept j && xKept j' && decide (j < j')) || !eqA 4060 xs[j]! xs[j']!) &&
  (allLt 35 fun j => !eqA 4060 xs[j]! (idA 4060)) &&
  (allLt 5 fun k => eqA 4060 xs[7 * k]! ruZA) &&
  eqA 4060 (powA 4060 ruC0A 20) (idA 4060) && !eqA 4060 g5A (idA 4060) &&
  (allLt 35 fun j => !eqA 4060 (compA 4060 g5A xs[j]!) (compA 4060 xs[j]! g5A) ||
    eqA 4060 xs[j]! ruZA)

@[expose] def ruB1XCheck : Bool := xCheckWith xList

@[expose] def conjBy (q : List Int × Array Nat × Array Nat) (t : Array Nat) : Array Nat :=
  compA 4060 (compA 4060 q.2.1 t) q.2.2

@[expose] def e8W : List (List Int × Array Nat × Array Nat) :=
  e8ConjWords.map fun w =>
    let s := wordA 4060 ruSGensA (ruSGensA.map ruInv) w
    (w, s, invCand 4060 s)

@[expose] def bigElt (es xs : Array (Array Nat)) (k : Nat) : Array Nat :=
  if k < 7 then es[k]! else xs[e8BigIdx.getD (k - 7) 0]!

@[expose] def pairCond (a b : Array Nat) : Bool :=
  !eqA 4060 b ruZA && !eqA 4060 b a && !eqA 4060 b (compA 4060 ruZA a) &&
    eqA 4060 (compA 4060 a b) (compA 4060 b a)

@[expose] def e8CheckWith (es xs : Array (Array Nat))
    (ws : List (List Int × Array Nat × Array Nat)) : Bool :=
  (e8ConjWords.all fun w => lettersOK 4 w) &&
  (ws.all fun q => isInvA 4060 q.2.1 q.2.2) &&
  all2 4060 ruLevS (fun t => !ruIsInvolA t ||
    (Nat.any 15 fun k _ => eqA 4060 t (bigElt es xs k)) ||
    decide (9 ≤ (pickBy (fun p p' => eqA 4060 p.2 p'.2) (ws.map fun q => (q, conjBy q t))).length)) &&
  (allLt 8 fun k => allLt 15 fun k' =>
    let a := bigElt es xs (7 + k)
    let b := bigElt es xs k'
    !pairCond a b || decide (9 ≤ (pickBy (fun p p' => eqA 4060 p.2.1 p'.2.1 &&
      eqA 4060 p.2.2 p'.2.2) (ws.map fun q => (q, conjBy q a, conjBy q b))).length))

@[expose] def ruB1E8Check : Bool := e8CheckWith ruEArr xList e8W

end CFSG.Sporadic.RuSchreier.RuB1
