module

public import Certificates.Data.Kernel.Spor.Raw

public section

namespace CFSG.KS.Raw

open CFSG.KC.Enum CFSG.KS

@[expose] noncomputable def lbindRun (n w P : Nat) (L : List Nat) : Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun i => Nat.beq i n)
    (fun a _ ih i => bAnd(Nat.beq a (pg w (mask w) P i), ih (Nat.succ i))) L

@[expose] noncomputable def lbindK (L : List Nat) (n w P : Nat) : Bool := lbindRun n w P L 0

end CFSG.KS.Raw

end
