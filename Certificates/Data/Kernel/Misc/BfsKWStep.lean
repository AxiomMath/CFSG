module

public import Certificates.Data.Kernel.Misc.BfsKW
public import CFSG.Certificates.Kernel.Common.Loop

public section

namespace CFSG.KD.BfsKW

open CFSG.KD.BfsK CFSG.KC.Loop

@[expose] noncomputable def stepAtW (st : Nat → Nat → Nat) (X PA PB : Nat → Nat)
    (n h s c p cn : Nat) : Bool :=
  Nat.blt h c && Nat.ble p c && Nat.blt p n && Nat.beq (X p) (st (X h) s) &&
    cond (Nat.beq p c)
      (Nat.beq cn (Nat.succ c) && Nat.beq (PA (Nat.pred c)) h && Nat.beq (PB (Nat.pred c)) s)
      (Nat.beq cn c)

@[expose] noncomputable def stepHW (R : Nat → Nat) (st : Nat → Nat → Nat) (o n k h s : Nat) :
    Bool :=
  stepAtW st (recX R o) (recFW R o 0) (recFW R o 1) n h s (recFW R o (Nat.add 4 s) h)
    (recFW R o (Nat.add (Nat.add 4 k) s) h)
    (cond (Nat.blt (Nat.succ s) k) (recFW R o (Nat.add 4 (Nat.succ s)) h)
      (recFW R o 4 (Nat.succ h)))

@[expose] noncomputable def stepRecW (R : Nat → Nat) (st : Nat → Nat → Nat) (o n k h : Nat) :
    Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun s ih => bAnd(stepHW R st o n k h s, ih)) k

@[expose] noncomputable def stepSlW (R : Nat → Nat) (st : Nat → Nat → Nat) (o n k j : Nat) :
    Bool :=
  allBelow 1024 16 fun l =>
    !(Nat.blt (Nat.add (Nat.mul j 1024) l) n) || stepRecW R st o n k (Nat.add (Nat.mul j 1024) l)

end CFSG.KD.BfsKW

end
