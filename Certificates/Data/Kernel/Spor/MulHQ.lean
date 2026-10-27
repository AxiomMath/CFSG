module

public import Certificates.Data.Kernel.Spor.MulH

public section

namespace CFSG.KS.MulH

open CFSG.KC.Enum

@[expose] noncomputable def bothK (k : Nat) (G GI : Nat → Nat) (j : Nat) : Nat :=
  nIf(Nat.blt j k, G j, GI (Nat.sub j k))

@[expose] noncomputable def prodQK (n w m K : Nat) (T S : Nat → Nat) (c : Nat) : Nat :=
  pcomp n w m (T (Nat.div c K)) (S (Nat.mod c K))

@[expose] noncomputable def conjQK (n w m K : Nat) (T C CI : Nat → Nat) (c : Nat) : Nat :=
  pcomp n w m (pcomp n w m (C (Nat.mod c K)) (T (Nat.div c K))) (CI (Nat.mod c K))

end CFSG.KS.MulH

end
