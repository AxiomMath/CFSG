module

public import Certificates.Data.CFSGNative.SectionRank.J4Local

public section

namespace CFSG.Quasithin.H13.NQCat.Native

open CFSG.SectionRank.Native CFSG.Sporadic.SmallF2.Native

@[expose] def j4R : Array (Array Nat) :=
  (ops2 112).regsOf j4Sylow11Data.seedA j4Sylow11Data.seedB j4Sylow11Data.nregs
    j4Sylow11Data.prog

@[expose] def j4X : Array Nat := j4R[22]!

@[expose] def j4Y : Array Nat := j4R[30]!

@[expose] def j4H : Array Nat := j4R[18]!

@[expose] def j4Z : Array Nat := (ops2 112).commM 11 j4X j4Y

@[expose] def j4Word (a b c : Nat) : Array Nat :=
  mulRows 112 (mulRows 112 (powRows 112 j4X a) (powRows 112 j4Y b)) (powRows 112 j4Z c)

@[expose] def lowBit (d v : Nat) : Nat := ((List.range d).find? fun j => v.testBit j).getD d

@[expose] def insertRref (d : Nat) (L : List (Nat × Nat × Nat)) (ic : Nat × Nat) :
    List (Nat × Nat × Nat) × Option Nat :=
  let ic' := L.foldl (fun (acc : Nat × Nat) (e : Nat × Nat × Nat) =>
    if acc.1.testBit e.1 then (acc.1 ^^^ e.2.1, acc.2 ^^^ e.2.2) else acc) ic
  if ic'.1 == 0 then (L, some ic'.2) else
    let p := lowBit d ic'.1
    (L.map (fun e => if e.2.1.testBit p then (e.1, e.2.1 ^^^ ic'.1, e.2.2 ^^^ ic'.2) else e) ++
      [(p, ic'.1, ic'.2)], none)

@[expose] def rrefImages (d : Nat) (img : Nat → Nat) : List (Nat × Nat × Nat) × List Nat :=
  (List.range d).foldl (fun (acc : List (Nat × Nat × Nat) × List Nat) i =>
    match insertRref d acc.1 (img i, 1 <<< i) with
    | (L, none) => (L, acc.2)
    | (L, some c) => (L, c :: acc.2)) ([], [])

@[expose] def rref (d : Nat) (vs : List Nat) : Array (Nat × Nat) :=
  ((vs.foldl (fun L v => (insertRref d L (v, 0)).1) []).map fun e => (e.1, e.2.1)).toArray

@[expose] def rrefOK (d : Nat) (A : Array (Nat × Nat)) : Bool :=
  A.all (fun e => decide (e.1 < d) && e.2.testBit e.1) &&
    (List.range A.size).all fun i => (List.range A.size).all fun j =>
      i == j || !((A[j]!).2.testBit (A[i]!).1)

@[expose] def colFixT (d : Nat) (T : Array Nat) (v : Nat) : Nat := vecMulN d T v ^^^ v

@[expose] def fixCertOK (d : Nat) (T : Array Nat) (K : Array (Nat × Nat))
    (I : Array (Nat × Nat × Nat)) (k : Nat) : Bool :=
  rrefOK d K && K.all (fun e => colFixT d T e.2 == 0) &&
    rrefOK d (I.map fun e => (e.1, colFixT d T e.2.2)) && K.size == k && K.size + I.size == d

@[expose] def fixDimOK (d : Nat) (M : Array Nat) (k : Nat) : Bool :=
  let T := transposeRows d M
  let R := rrefImages d fun i => colFixT d T (1 <<< i)
  fixCertOK d T (rref d R.2) R.1.toArray k

@[expose] def powTable (M : Array Nat) : List (Array Nat) := (List.range 11).map (powRows 112 M)

@[expose] def j4FixNoncentralOK : Bool :=
  let XP := powTable j4X
  let YP := powTable j4Y
  let ZP := powTable j4Z
  (List.range 11).all fun i => (List.range 11).all fun j =>
    (i == 0 && j == 0) ||
      (let W := mulRows 112 (XP.getD i #[]) (YP.getD j #[])
       (List.range 11).all fun k => fixDimOK 112 (mulRows 112 W (ZP.getD k #[])) 12)

@[expose] def j4FixCentralOK : Bool :=
  let ZP := powTable j4Z
  (List.range 11).all fun k => k == 0 || fixDimOK 112 (ZP.getD k #[]) 2

@[expose] def j4PowXYOK : Bool :=
  let XP := powTable j4X
  let YP := powTable j4Y
  (List.range 11).all fun i => (List.range 11).all fun j =>
    (ops2 112).eq ((ops2 112).pow (mulRows 112 (XP.getD i #[]) (YP.getD j #[])) 11)
      (ops2 112).one

end CFSG.Quasithin.H13.NQCat.Native
