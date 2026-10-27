module

public import CFSG.Certificates.Kernel.Enum.Defs

public section

namespace CFSG.KS.Row

open CFSG.KC.Enum

@[expose] noncomputable def rg (w m : Nat) (F : Nat → Nat) (o i : Nat) : Nat :=
  fld(F (Nat.add o (Nat.shiftRight i (nat_lit 5))), Nat.mul w (Nat.land i (nat_lit 31)), m)

@[expose] noncomputable def rpermK (n w m : Nat) (F : Nat → Nat) (o : Nat) (G : Nat → Nat)
    (o' : Nat) : Bool :=
  allN n (fun i => strictB (rg w m F o i) (fun v =>
    bAnd(Nat.blt v n, Nat.beq (rg w m G o' v) i)))

end CFSG.KS.Row

end
