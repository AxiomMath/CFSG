module

public import Certificates.Data.Kernel.Spor.PEnum

public section

namespace CFSG.KC.Fi23S

open CFSG.KC.Enum CFSG.KS.PEnum

@[expose] noncomputable def wF (L : Nat → Nat → Nat) (PAR LAB : Nat → Nat) (f : Nat) :
    Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ x => x)
    (fun _ ih k x => Bool.rec (motive := fun _ => Nat) x (L (r32 LAB k) (ih (r32 PAR k) x))
      (bAnd(Nat.blt (nat_lit 0) k, Nat.blt (r32 PAR k) k))) f

@[expose] noncomputable def cyK (h : Nat → Nat) (q : Nat) (f : Nat) : Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun l x => nIf(Nat.beq x q, l, nat_lit 0))
    (fun _ ih l x => nIf(Nat.beq x q, l, ih (Nat.succ l) (h x))) f

end CFSG.KC.Fi23S

end
