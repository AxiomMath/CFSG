module

public import Certificates.Data.Kernel.E27Orth.Orth

public section

namespace CFSG.KC.E27Orth

open CFSG.KC.Misc.G24

@[expose] noncomputable def spOK (n J X : Nat) : Bool :=
  Nat.beq (mulF2 n (mulF2 n (trF2 n X) J) X) J

end CFSG.KC.E27Orth

end
