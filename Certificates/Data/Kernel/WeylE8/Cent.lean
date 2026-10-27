module

public import Certificates.Data.Kernel.WeylE8.Refl

public section

namespace CFSG.KLC.E8

open CFSG.KC.Enum CFSG.KS

@[expose] noncomputable def notB' (b : Bool) : Bool := Bool.rec (motive := fun _ => Bool) true false b

@[expose] noncomputable def dFixAt (ST : Nat → Nat) (r m : Nat) : Bool :=
  bAnd(Nat.blt m (nat_lit 256), bAnd(Nat.beq (Nat.land (pop8 m) (nat_lit 1)) (nat_lit 0),
    bAnd(Nat.blt (nat_lit 0) m, Nat.beq (pg (nat_lit 8) (nat_lit 255) (ST m) r) r)))

@[expose] noncomputable def dFixK (ST : Nat → Nat) (DW : Nat) : Bool :=
  allN (nat_lit 112) fun r => dFixAt ST r (pg (nat_lit 8) (nat_lit 255) DW r)

@[expose] noncomputable def sOrbAt (ST : Nat → Nat) (r m : Nat) : Bool :=
  bAnd(Nat.blt m (nat_lit 256), bAnd(Nat.beq (Nat.land (pop8 m) (nat_lit 1)) (nat_lit 0),
    Nat.beq (pg (nat_lit 8) (nat_lit 255) (ST m) (nat_lit 112)) r))

@[expose] noncomputable def sOrbK (ST : Nat → Nat) (SW : Nat) : Bool :=
  allN (nat_lit 240) fun r => bIf(Nat.blt r (nat_lit 112), true,
    sOrbAt ST r (pg (nat_lit 8) (nat_lit 255) SW r))

@[expose] noncomputable def frameAt (RT : Nat → Nat) (k w : Nat) : Bool :=
  bAnd(Nat.blt w (nat_lit 16384), Nat.beq (pg (nat_lit 8) (nat_lit 255)
    (RT (Nat.add (nat_lit 112) (Nat.land w (nat_lit 127))))
    (Nat.add (nat_lit 112) (Nat.shiftRight w (nat_lit 7)))) k)

@[expose] noncomputable def frameReflK (RT : Nat → Nat) (KP FW : Nat) : Bool :=
  allN (nat_lit 8) fun i => frameAt RT (pg (nat_lit 8) (nat_lit 255) KP i)
    (pg (nat_lit 14) (nat_lit 16383) FW i)

@[expose] noncomputable def wt2K (ST : Nat → Nat) : Bool :=
  allN (nat_lit 256) fun m => bIf(Nat.beq (Nat.land (pop8 m) (nat_lit 1)) (nat_lit 0),
    bIf(Nat.beq m (nat_lit 0), true,
      Bool.rec (motive := fun _ => Bool) (notB' (Nat.beq (pop8 m) (nat_lit 2)))
        (Nat.beq (pop8 m) (nat_lit 2)) (Nat.beq (fixCntK (nat_lit 240) (nat_lit 8) (ST m)) (nat_lit 60))),
    true)

@[expose] noncomputable def tripleK : Bool :=
  allN (nat_lit 256) fun a => bIf(Nat.beq (pop8 a) (nat_lit 2),
    allN (nat_lit 256) (fun b => bIf(bAnd(Nat.beq (pop8 b) (nat_lit 2),
        Nat.beq (pop8 (Nat.xor a b)) (nat_lit 2)),
      allN (nat_lit 256) (fun c => bIf(bAnd(Nat.beq (pop8 c) (nat_lit 2),
          bAnd(Nat.beq (pop8 (Nat.xor a c)) (nat_lit 2), bAnd(Nat.beq (pop8 (Nat.xor b c)) (nat_lit 2),
            notB' (Nat.beq c (Nat.xor a b))))),
        Nat.blt (nat_lit 0) (Nat.land a (Nat.land b c)), true)),
      true)),
    true)

@[expose] noncomputable def pair2K : Bool :=
  allN (nat_lit 256) fun a => bIf(Nat.beq (pop8 a) (nat_lit 2),
    allN (nat_lit 256) (fun b => bIf(bAnd(Nat.beq (pop8 b) (nat_lit 2),
        Nat.beq (pop8 (Nat.xor a b)) (nat_lit 2)),
      Nat.ble (pop8 (Nat.land a b)) (nat_lit 1), true)),
    true)

end CFSG.KLC.E8

end
