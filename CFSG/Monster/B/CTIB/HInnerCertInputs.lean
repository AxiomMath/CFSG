module

public import Certificates.Data.CFSGNative.CTIB.Census
public meta import Certificates.Data.CFSGNative.CTIB.Census

public section

namespace CFSG.Monster.B.CTIB

open CFSG.Monster.B.CTIB.Native CFSG.Monster.B.Max2.Native

@[expose] def innerTab : Array Nat := Id.run do
  let mut t : Array Nat := Array.replicate (2 ^ 22) 0
  for k in [0:5] do
    let r := censusRecs.getD k (0, 0)
    for p in (natBfs censusAct 2 r.1 (r.2 + 1)).1 do
      t := t.set! p (k + 1)
  return t

@[expose] def innerTabOK (t : Array Nat) : Bool :=
  (List.range 5).all fun k =>
    (natBfs censusAct 2 (censusRecs.getD k (0, 0)).1 ((censusRecs.getD k (0, 0)).2 + 1)).1.all
      fun p => t[p]! == k + 1

@[expose] def innerTy (t : Array Nat) (n : Nat) : Nat :=
  if n % 2 ^ 22 = 0 then (if n = 0 then 0 else 6) else t[n % 2 ^ 22]!

@[expose] def innerTyRank (k : Nat) : Nat := [0, 1860, 2048, 2168, 1, 1, 2048].getD k 0

@[expose] def innerPairIdx (a b : Nat) : Nat :=
  if a = 2048 ∧ b = 1860 then 1 else if a = 1860 ∧ b = 2048 then 2
  else if a = 2048 ∧ b = 2168 then 3 else if a = 2168 ∧ b = 2048 then 4
  else if a = 2168 ∧ b = 2168 then 5 else if a = 1 then 6
  else if a = 0 ∧ b = 1860 then 7 else if a = 1860 ∧ b = 0 then 8 else 9

@[expose] def innerKey (t : Array Nat) (n : Nat) : Nat :=
  if qmul gArr n 1 = qmul gArr 1 n then
    innerPairIdx (innerTyRank (innerTy t n)) (innerTyRank (innerTy t (qmul gArr 1 n)))
  else 0

@[expose] def innerHist (t : Array Nat) : Array Nat :=
  Nat.fold (2 ^ 23) (fun n _ h => h.modify (innerKey t n) (· + 1)) (Array.replicate 10 0)

@[expose] def innerRepsOK (t : Array Nat) : Bool :=
  [2, 4, 32, 16384, 802816].all (fun f => qmul gArr f 1 == qmul gArr 1 f &&
    innerTy t f == 1 && innerTy t (qmul gArr 1 f) == 2) &&
  qmul gArr 2 4 == 6 && qmul gArr 4 2 == 6 &&
  qmul gArr 32 16384 == 16416 && qmul gArr 16384 32 == 16416 &&
  qmul gArr 32 802816 == 802848 && qmul gArr 802816 32 == 802848 &&
  qmul gArr 16384 802816 == 786432 && qmul gArr 802816 16384 == 786432 &&
  qmul gArr 16416 802816 == 786464 &&
  [6, 16416, 802848, 786432].all (fun p => innerTy t p == 2 && innerTy t (qmul gArr 1 p) == 3) &&
  innerTy t 786464 == 3 && innerTy t (qmul gArr 1 786464) == 3 &&
  innerTy t (2 ^ 22) == 6 && innerTy t (qmul gArr 1 (2 ^ 22)) == 1

@[expose] def innerOrbOK (_ : Unit := ()) : Bool :=
  (List.range 5).all fun k => orbitOK censusAct 2 (fun v => decide (0 < v) && decide (v < 2 ^ 22))
    (censusRecs.getD k (0, 0)).1 (censusRecs.getD k (0, 0)).2

end CFSG.Monster.B.CTIB
