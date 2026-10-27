module

public import Certificates.Data.Kernel.SporSch.HNF5

public section

namespace CFSG.KS.SporSch

open CFSG.KC.Enum

@[expose] noncomputable def subRow5 (T : Nat → Nat) (i : Nat) : Nat :=
  red5 (Nat.add (T i) (Nat.shiftLeft (nat_lit 4) (Nat.mul (nat_lit 16) i)))

@[expose] noncomputable def diagRow5 (r i : Nat) : Nat := nIf(Nat.blt i r, idRow5 i, nat_lit 0)

end CFSG.KS.SporSch

end
