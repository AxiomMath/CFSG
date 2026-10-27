module

public import Certificates.Data.Kernel.O8.SA

public section

namespace CFSG.KC.O8

open CFSG.KC.Enum CFSG.KS

@[expose] noncomputable def labK (LT i : Nat) : Nat := fld(LT, Nat.mul (nat_lit 3) i, nat_lit 7)

@[expose] noncomputable def parF (PT LT f : Nat) : Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun _ => nat_lit 0)
    (fun _ ih i => nIf(Nat.beq i (nat_lit 0), nat_lit 0,
      Nat.xor (strictN (ix13 PT i) ih)
        (nIf(Nat.beq (labK LT i) (nat_lit 4), nat_lit 1, nat_lit 0)))) f

@[expose] noncomputable def parK (PT LT i : Nat) : Nat := parF PT LT (nat_lit 8192) i

@[expose] noncomputable def ycK (SC YI : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun k ih => strictN ih fun a =>
      Nat.lor a (Nat.shiftLeft (saAtK SC (ix13 YI k)) (Nat.mul (nat_lit 64) k))) (nat_lit 38)

@[expose] noncomputable def tyLK (YP : Nat) (TY : Nat → Nat) (t : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun k ih => strictN ih fun a => nIf(Nat.beq (TY k) t,
      Nat.lor (Nat.shiftLeft a (nat_lit 71)) (Nat.lor (nat_lit 1180591620717411303424)
        (Nat.lor (Nat.shiftLeft (saAtK YP k) (nat_lit 6)) k)), a)) (nat_lit 38)

@[expose] noncomputable def lookL (L s : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun _ => nat_lit 0)
    (fun _ ih L => nIf(Nat.beq L (nat_lit 0), nat_lit 0,
      nIf(Nat.beq (fld(L, nat_lit 6, nat_lit 18446744073709551615)) s,
        Nat.succ (Nat.land L (nat_lit 63)), strictN (Nat.shiftRight L (nat_lit 71)) ih)))
    (nat_lit 38) L

@[expose] noncomputable def vecK (NS NI P v : Nat) : Nat :=
  pg (nat_lit 8) (nat_lit 255) NS (pg (nat_lit 9) (nat_lit 511) P (pg (nat_lit 8) (nat_lit 255) NI v))

@[expose] noncomputable def matOfK (NS NI : Nat) (SA SB : Nat → Nat) (P : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun c ih => Nat.lor ih (Nat.shiftLeft (Nat.xor (vecK NS NI P (SA c)) (vecK NS NI P (SB c)))
      (Nat.mul (nat_lit 8) c))) (nat_lit 8)

@[expose] noncomputable def mpowK (x m : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) idK (fun _ ih => strictN ih fun a => matMulK a x) m

@[expose] noncomputable def critM (X J : Nat) (W : List (Nat × Nat × Nat)) : Bool :=
  strictB (matMulK J X) fun Ji =>
  List.rec (motive := fun _ => Bool) false (fun w _ ih =>
    strictB (mpowK (matMulK (matMulK (matMulK Ji w.1) J) w.2.1) w.2.2) fun g =>
      bIf(bAnd(Nat.beq (matMulK g (matMulK g g)) idK, bIf(Nat.beq g idK, false, true)), true, ih)) W

@[expose] noncomputable def scanAt (SC PT LT L2 X : Nat) (W : List (Nat × Nat × Nat)) (i : Nat) :
    Bool :=
  bIf(Nat.beq (parK PT LT i) (nat_lit 1),
    strictB (saAtK SC i) fun a => strictB (matMulK a a) fun s =>
      bAnd(Nat.beq (lookL L2 s) (nat_lit 0), bIf(Nat.beq s X, critM X a W, true)),
    true)

@[expose] noncomputable def recAt (SC PT LT L1 i : Nat) : Nat :=
  strictN (saAtK SC i) fun a => strictN (lookL L1 (matMulK a a)) fun k =>
    nIf(Nat.beq k (nat_lit 0), nat_lit 0,
      Nat.add (Nat.add (nat_lit 1048576) (Nat.mul (nat_lit 128) i))
        (Nat.add (Nat.mul (nat_lit 2) (Nat.sub k (nat_lit 1))) (parK PT LT i)))

@[expose] noncomputable def rootsK (SC PT LT L1 : Nat) : Nat :=
  foldN (nat_lit 8192) (fun i acc => strictN (recAt SC PT LT L1 i) fun r =>
    nIf(Nat.beq r (nat_lit 0), acc, Nat.lor (Nat.shiftLeft acc (nat_lit 21)) r)) (nat_lit 0)

@[expose] noncomputable def recAll (R : Nat) (f : Nat → Bool) : Bool :=
  Nat.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun _ ih R => bIf(Nat.beq R (nat_lit 0), true,
      bAnd(f (Nat.land R (nat_lit 2097151)), strictB (Nat.shiftRight R (nat_lit 21)) ih)))
    (nat_lit 8192) R

@[expose] noncomputable def recI (r : Nat) : Nat := fld(r, nat_lit 7, nat_lit 8191)

@[expose] noncomputable def recR (r : Nat) : Nat := fld(r, nat_lit 1, nat_lit 63)

@[expose] noncomputable def recP (r : Nat) : Nat := Nat.land r (nat_lit 1)

@[expose] noncomputable def pairK (SC YP R : Nat) : Bool :=
  recAll R fun a => bIf(Nat.beq (recP a) (nat_lit 1),
    strictB (recR a) fun k => strictB (saAtK SC (recI a)) fun j => strictB (saAtK YP k) fun y =>
      recAll R fun b => bIf(bAnd(Nat.beq (recP b) (nat_lit 0), Nat.beq (recR b) k),
        strictB (saAtK SC (recI b)) fun u =>
          bIf(Nat.beq (matMulK j u) (matMulK (matMulK u y) j), false, true),
        true),
    true)

@[expose] noncomputable def fix360K (P : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun p ih => Nat.add ih (nIf(Nat.beq (pg (nat_lit 9) (nat_lit 511) P p) p, nat_lit 1, nat_lit 0)))
    (nat_lit 360)

end CFSG.KC.O8

end
