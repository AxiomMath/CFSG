module

public import CFSG.Certificates.Kernel.Enum.Defs

public section

namespace CFSG.KS.Ru2254

open CFSG.KC.Enum

@[expose] noncomputable def fixCntK (n : Nat) (f : Nat → Nat) : Nat :=
  foldN n (fun x s => Nat.add s (nIf(Nat.beq (f x) x, nat_lit 1, nat_lit 0))) (nat_lit 0)

end CFSG.KS.Ru2254

end
