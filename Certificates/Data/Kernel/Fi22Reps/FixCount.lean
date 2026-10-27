module

public import Certificates.Data.Kernel.Fi22S0.Check

public section

namespace CFSG.KC.Fi22Reps

open CFSG.KC.Fi22S0

@[expose] noncomputable def fixCntK (X : Nat) : Nat :=
  ((List.range 3510).filter fun i => ent X i == i).length

end CFSG.KC.Fi22Reps
