module

public import Certificates.Data.Kernel.OpsF2K
public import CFSG.Quasithin.H13.NQCatJ4Native

public section

namespace CFSG.KC.J4Fix

open CFSG.KC.M1F2 CFSG.KLie.CT CFSG.Quasithin.H13.NQCat.Native

@[expose] noncomputable def transF (d X : Nat) : Nat :=
  (List.range d).foldl (fun acc i =>
    let r := rowF d X i
    (List.range d).foldl (fun acc j =>
      if r.testBit j then acc ||| (1 <<< (d * j + i)) else acc) acc) 0

@[expose] noncomputable def colFixK (d T v : Nat) : Nat := vmF d T v ^^^ v

@[expose] def rrefL (d : Nat) (vs : List Nat) : List (Nat × Nat) :=
  (vs.foldl (fun L v => (insertRref d L (v, 0)).1) []).map fun e => (e.1, e.2.1)

@[expose] def rrefOKL (d : Nat) (A : List (Nat × Nat)) : Bool :=
  A.all (fun e => decide (e.1 < d) && e.2.testBit e.1) &&
    A.zipIdx.all fun e => A.zipIdx.all fun f => e.2 == f.2 || !(f.1.2.testBit e.1.1)

@[expose] noncomputable def fixCertK (d T : Nat) (K : List (Nat × Nat))
    (I : List (Nat × Nat × Nat)) (k : Nat) : Bool :=
  rrefOKL d K && K.all (fun e => colFixK d T e.2 == 0) &&
    rrefOKL d (I.map fun e => (e.1, colFixK d T e.2.2)) && K.length == k &&
    K.length + I.length == d

@[expose] noncomputable def fixDimK (d X k : Nat) : Bool :=
  let T := transF d X
  let R := rrefImages d fun i => colFixK d T (1 <<< i)
  fixCertK d T (rrefL d R.2) R.1 k

@[expose] noncomputable def powLK (d M : Nat) : Nat → Nat
  | 0 => idF d
  | e + 1 => mulF d (powLK d M e) M

@[expose] noncomputable def wordK (d X Y Z a b c : Nat) : Nat :=
  mulF d (mulF d (powLK d X a) (powLK d Y b)) (powLK d Z c)

@[expose] noncomputable def fixRepsK (d X Y Z : Nat) : Bool :=
  fixDimK d (wordK d X Y Z 0 1 0) 12 &&
    (List.range 11).all fun b => fixDimK d (wordK d X Y Z 1 b 0) 12

@[expose] noncomputable def colCF (d X j : Nat) : Nat :=
  orN d fun i => nIf(bit X (d * i + j), nat_lit 1, nat_lit 0) <<< (1 * i)

@[expose] noncomputable def transCF (d X : Nat) : Nat :=
  orN d fun j => colCF d X j <<< (d * j)

@[expose] noncomputable def lowBitRK (d v m : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) d (fun k ih => nIf(Nat.blt ih d, ih, nIf(bit v k, k, d))) m

@[expose] noncomputable def redRK (L : List (Nat × Nat × Nat)) : Nat × Nat → Nat × Nat :=
  List.rec (motive := fun _ => Nat × Nat → Nat × Nat) (fun ic => ic)
    (fun e _ ih ic => ih (Bool.rec (motive := fun _ => Nat × Nat) ic
      (Nat.xor ic.1 e.2.1, Nat.xor ic.2 e.2.2) (bit ic.1 e.1))) L

@[expose] noncomputable def clrRK (p v c : Nat) (L : List (Nat × Nat × Nat)) :
    List (Nat × Nat × Nat) :=
  List.rec (motive := fun _ => List (Nat × Nat × Nat)) [(p, v, c)]
    (fun e _ ih => Bool.rec (motive := fun _ => List (Nat × Nat × Nat)) (e :: ih)
      ((e.1, Nat.xor e.2.1 v, Nat.xor e.2.2 c) :: ih) (bit e.2.1 p)) L

@[expose] noncomputable def stepRK (d : Nat) (acc : List (Nat × Nat × Nat) × List Nat)
    (ic : Nat × Nat) : List (Nat × Nat × Nat) × List Nat :=
  (fun r => Bool.rec (motive := fun _ => List (Nat × Nat × Nat) × List Nat)
      (clrRK (lowBitRK d r.1 d) r.1 r.2 acc.1, acc.2) (acc.1, r.2 :: acc.2) (Nat.beq r.1 0))
    (redRK acc.1 ic)

@[expose] noncomputable def rrefImK (d : Nat) (img : Nat → Nat) :
    List (Nat × Nat × Nat) × List Nat :=
  Nat.rec (motive := fun _ => List (Nat × Nat × Nat) × List Nat) ([], [])
    (fun i acc => stepRK d acc (img i, 1 <<< i)) d

@[expose] noncomputable def pivOKR (d : Nat) : List (Nat × Nat) → Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true) (fun e _ ih acc =>
    andB (andB (Nat.blt e.1 d) (Nat.blt 0 (Nat.land e.2 (Nat.shiftLeft 1 e.1))))
      (andB (Nat.beq (Nat.land acc (Nat.shiftLeft 1 e.1)) 0)
        (ih (Nat.lor acc (Nat.shiftLeft 1 e.1)))))

@[expose] noncomputable def pivMaskR : List (Nat × Nat) → Nat :=
  List.rec (motive := fun _ => Nat) 0 (fun e _ ih => Nat.lor (Nat.shiftLeft 1 e.1) ih)

@[expose] noncomputable def clrOKR (P : Nat) : List (Nat × Nat) → Bool :=
  List.rec (motive := fun _ => Bool) true (fun e _ ih =>
    andB (Nat.beq (Nat.land e.2 P) (Nat.shiftLeft 1 e.1)) ih)

@[expose] noncomputable def rrefOKK (d : Nat) (A : List (Nat × Nat)) : Bool :=
  andB (pivOKR d A 0) (clrOKR (pivMaskR A) A)

@[expose] noncomputable def fixCertFK (d T : Nat) (K : List (Nat × Nat))
    (I : List (Nat × Nat × Nat)) (k : Nat) : Bool :=
  rrefOKK d K && K.all (fun e => colFixK d T e.2 == 0) &&
    rrefOKK d (I.map fun e => (e.1, colFixK d T e.2.2)) && K.length == k &&
    K.length + I.length == d

@[expose] noncomputable def fixDimFK (d X k : Nat) : Bool :=
  let T := transCF d X
  let R := rrefImK d fun i => colFixK d T (1 <<< i)
  fixCertFK d T (rrefL d R.2) R.1 k

@[expose] noncomputable def fixRepsFK (d X Y Z : Nat) : Bool :=
  fixDimFK d (wordK d X Y Z 0 1 0) 12 &&
    (List.range 11).all fun b => fixDimFK d (wordK d X Y Z 1 b 0) 12

open CFSG.KC.OpsF2K CFSG.SectionRank.Native in
@[expose] noncomputable def regsK (A B : Nat) : List Nat :=
  runK 112 A B j4Sylow11Data.nregs j4Sylow11Data.prog

@[expose] noncomputable def xK (A B : Nat) : Nat := CFSG.KC.OpsF2K.getR 112 (regsK A B) 22

@[expose] noncomputable def yK (A B : Nat) : Nat := CFSG.KC.OpsF2K.getR 112 (regsK A B) 30

@[expose] noncomputable def hK (A B : Nat) : Nat := CFSG.KC.OpsF2K.getR 112 (regsK A B) 18

@[expose] noncomputable def zK (A B : Nat) : Nat := CFSG.KC.OpsF2K.commMK 112 11 (xK A B) (yK A B)

end CFSG.KC.J4Fix

end
