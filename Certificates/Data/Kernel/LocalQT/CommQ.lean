module

public import Certificates.Data.Kernel.Spor.MulHQ

public section

namespace CFSG.KS.MulH

open CFSG.KC.Enum

@[expose] noncomputable def commQK (n w m K : Nat) (C CI : Nat → Nat) (c : Nat) : Nat :=
  pcomp n w m (pcomp n w m (pcomp n w m (C (Nat.div c K)) (C (Nat.mod c K))) (CI (Nat.div c K)))
    (CI (Nat.mod c K))

end CFSG.KS.MulH

end
