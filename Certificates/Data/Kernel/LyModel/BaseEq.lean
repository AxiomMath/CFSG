module

public import CFSG.Certificates.Kernel.YModel.NetSem
public import Mathlib.Data.Vector.Basic
public import Mathlib.GroupTheory.Perm.Basic

public section

namespace CFSG.KC.LyModel

open CFSG.KC CFSG.KC.YModel.Sem

@[expose] noncomputable def baseEq (Ns Ms : List Nat) : Bool :=
  andB (Nat.beq (compN 17 Ns 0) (compN 17 Ms 0))
    (andB (Nat.beq (compN 17 Ns 3) (compN 17 Ms 3)) (Nat.beq (compN 17 Ns 1) (compN 17 Ms 1)))

end CFSG.KC.LyModel

end
