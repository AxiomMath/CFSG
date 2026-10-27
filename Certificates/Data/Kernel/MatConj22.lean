module

public import CFSG.Certificates.Kernel.Lie.CT.Core

public section

namespace CFSG.KC.MatConj

open CFSG.KLie.CT

@[expose] noncomputable def ones22 : Nat :=
  0x40000100000400001000004000010000040000100000400001000004000010000040000100000400001000004000010000040000100000400001

@[expose] noncomputable def mulR (g n : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun b acc => Nat.xor acc (Nat.mul (Nat.land (Nat.shiftRight n b) ones22) (fget g b 22)))
    (nat_lit 22)

@[expose] noncomputable def mulL (c u : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun a acc => Nat.xor acc (Nat.mul (fget c a 484) (fget u a 22))) (nat_lit 22)

@[expose] noncomputable def forceN (y : Nat) (k : Nat → Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (k (nat_lit 0)) (fun m _ => k (Nat.succ m)) y

@[expose] noncomputable def conjM (g c n : Nat) : Nat := forceN (mulR g n) (mulL c)

end CFSG.KC.MatConj

end
