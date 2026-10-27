module

public import CFSG.Certificates.Kernel.Enum.Defs
public import CFSG.Certificates.Kernel.Lie.CT.Core

public section

namespace CFSG.KC.Fi24Pl

open CFSG.KC.Enum

@[expose] noncomputable def baseP : Nat := nat_lit 211312659660804

@[expose] noncomputable def bp (r : Nat) : Nat := pg (nat_lit 9) (nat_lit 511) baseP r

@[expose] noncomputable def aK (F k y : Nat) : Nat :=
  pg (nat_lit 9) (nat_lit 511) F (Nat.add (Nat.mul (nat_lit 504) k) y)

@[expose] noncomputable def aPow (F k d y : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) y (fun _ ih => aK F k ih) d

@[expose] noncomputable def dg (i p : Nat) : Nat := Nat.mod (Nat.div i p) (nat_lit 3)

@[expose] noncomputable def iotaPt (F i y : Nat) : Nat :=
  aPow F (nat_lit 0) (dg i (nat_lit 1)) (aPow F (nat_lit 1) (dg i (nat_lit 3))
    (aPow F (nat_lit 2) (dg i (nat_lit 9)) (aPow F (nat_lit 3) (dg i (nat_lit 27))
      (aPow F (nat_lit 4) (dg i (nat_lit 81)) y))))

@[expose] noncomputable def basisK (F : Nat) : Bool :=
  allN (nat_lit 5) fun k => allN (nat_lit 504) fun x =>
    bAnd(Nat.blt (aK F k x) (nat_lit 504), Nat.beq (aK F k (aK F k (aK F k x))) x)

@[expose] noncomputable def iotaK (F : Nat) (IK : Nat → Nat) (i : Nat) : Bool :=
  strictB (IK i) fun p => allN (nat_lit 504) fun x =>
    Nat.beq (pg (nat_lit 9) (nat_lit 511) p x) (iotaPt F i x)

@[expose] noncomputable def invK (IK V : Nat → Nat) : Bool :=
  allN (nat_lit 243) fun i => strictB (IK i) fun p => strictB (V i) fun v =>
    allN (nat_lit 6) fun r => strictB (pg (nat_lit 9) (nat_lit 511) v r) fun y =>
      bAnd(Nat.blt y (nat_lit 504), Nat.beq (pg (nat_lit 9) (nat_lit 511) p y) (bp r))

@[expose] noncomputable def mIdx (MK : Nat → Nat) (k j : Nat) : Nat :=
  fld(MK k, Nat.mul (nat_lit 16) j, nat_lit 65535)

@[expose] noncomputable def normK (F : Nat) (G T MK : Nat → Nat) : Bool :=
  allN (nat_lit 5) fun k => allN (nat_lit 12) fun j => strictB (mIdx MK k j) fun m =>
    bAnd(Nat.blt m (nat_lit 4096), strictB (G j) fun g => strictB (T m) fun q =>
      allN (nat_lit 504) fun x =>
        Nat.beq (aK F k (pg (nat_lit 9) (nat_lit 511) g x))
          (pg (nat_lit 9) (nat_lit 511) q (aK F k x)))

@[expose] noncomputable def bitK (IK V : Nat → Nat) (q i : Nat) : Bool :=
  strictB (IK i) fun p => strictB (V i) fun v =>
    allN (nat_lit 6) fun r =>
      Nat.beq (pg (nat_lit 9) (nat_lit 511) p
        (pg (nat_lit 9) (nat_lit 511) q (pg (nat_lit 9) (nat_lit 511) v r)))
        (pg (nat_lit 9) (nat_lit 511) q (bp r))

@[expose] noncomputable def rowK (IK V T BT : Nat → Nat) (t : Nat) : Bool :=
  strictB (T t) fun q => strictB (BT t) fun b =>
    bAnd(Nat.beq (Nat.shiftRight b (nat_lit 243)) (nat_lit 0),
      allN (nat_lit 243) fun i =>
        Nat.beq fld(b, i, nat_lit 1) (Bool.rec (motive := fun _ => Nat) (nat_lit 0) (nat_lit 1)
          (bitK IK V q i)))

@[expose] noncomputable def rowC (IK V T BT : Nat → Nat) (c : Nat) : Bool :=
  allN (nat_lit 64) fun l => rowK IK V T BT (Nat.add (Nat.mul (nat_lit 64) c) l)

@[expose] noncomputable def popK (b : Nat) : Nat :=
  CFSG.KLie.CT.sumN (nat_lit 243) fun i => fld(b, i, nat_lit 1)

@[expose] noncomputable def sameK (BT : Nat → Nat) (b : Nat) : Nat :=
  CFSG.KC.Loop.sumBelow (nat_lit 4096) (nat_lit 64) fun s =>
    Bool.rec (motive := fun _ => Nat) (nat_lit 0) (nat_lit 1)
      (CFSG.KLie.CT.orB (Nat.beq s (nat_lit 0)) (Nat.beq (BT s) b))

@[expose] noncomputable def finalAt (BT : Nat → Nat) (t : Nat) : Bool :=
  strictB (BT t) fun b => strictB (popK b) fun c =>
    CFSG.KLie.CT.orB (Nat.beq t (nat_lit 0)) (CFSG.KLie.CT.orB (Nat.blt c (nat_lit 81))
      (bAnd(Nat.beq c (nat_lit 81), Nat.ble (sameK BT b) (nat_lit 4))))

@[expose] noncomputable def finalK (BT : Nat → Nat) : Bool :=
  allN (nat_lit 4096) (finalAt BT)

end CFSG.KC.Fi24Pl

end
