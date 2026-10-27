module

public import Certificates.Data.Kernel.Misc.Sp6Transv

public section

namespace CFSG.KC.Misc.Sp6SR

open CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KD.Sp62 CFSG.KC.Misc.Clos CFSG.KC.Misc.Sp6Transv

@[expose] noncomputable def interN (nT nQ : Nat) (E S EQ NB : Nat → Nat) (c ci k : Nat) : Bool :=
  letB (E k) fun x => letB (NB k) fun r =>
    Bool.rec (motive := fun _ => Bool)
      (letB (MULF (MULF ci x) c) fun y =>
        andB (Nat.ble r nT)
          (andB (impB (Nat.blt 0 r) (Nat.blt (E (S (Nat.pred r))) y))
            (impB (Nat.blt r nT) (Nat.blt y (E (S r))))))
      (letB (Nat.sub r 1048576) fun j => andB (Nat.blt j nQ) (Nat.beq (EQ j) x))
      (Nat.ble 1048576 r)

@[expose] noncomputable def pairE (TE EZ : Nat → Nat) (r : Nat) : Nat :=
  MULF (TE (Nat.mod r 512)) (EZ (Nat.div r 512))

@[expose] noncomputable def wordO (O : Nat → Nat) (n v : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun _ => ONE)
    (fun _ ih v => MULF (O (Nat.mod v 128)) (ih (Nat.div v 128))) n v

@[expose] noncomputable def ocF (O : Nat → Nat) (s k : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat) (O k) s (Nat.beq k 126)

@[expose] noncomputable def digitsIn (lo hi n v : Nat) : Bool :=
  Nat.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun _ ih v => letB (Nat.mod v 128) fun d =>
      andB (orB (Nat.beq d 126) (andB (Nat.ble lo d) (Nat.blt d hi))) (ih (Nat.div v 128))) n v

@[expose] noncomputable def memAt (E : Nat → Nat) (off n x i : Nat) : Bool :=
  andB (Nat.blt i n) (Nat.beq (E (Nat.add off i)) x)

@[expose] noncomputable def commOrS (s q y : Nat) : Bool :=
  letB (MULF q y) fun a => letB (MULF y q) fun b => orB (Nat.beq a b) (Nat.beq a (MULF s b))

@[expose] noncomputable def witNC (E : Nat → Nat) (n q w : Nat) : Bool :=
  andB (Nat.blt w n) (Bool.not (commF (E w) q))

end CFSG.KC.Misc.Sp6SR

end
