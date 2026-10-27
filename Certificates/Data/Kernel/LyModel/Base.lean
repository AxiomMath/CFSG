module

public import CFSG.Certificates.Kernel.YModel.NetSem
public import CFSG.LieType.Multipliers.CoverWords
public import CFSG.Certificates.CosetTableShort
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.Open.Defs

public section

namespace CFSG.KC.LyModel

open CFSG.KC CFSG.KC.YModel.Sem

@[expose] noncomputable def baseFix (Ns : List Nat) : Bool :=
  andB (Nat.beq (compN 17 Ns 0) 0) (andB (Nat.beq (compN 17 Ns 3) 3) (Nat.beq (compN 17 Ns 1) 1))

@[expose] noncomputable def yIdx (l : Fin 6 × Bool) : Nat :=
  nIf(Nat.beq l.1.val 5, 0, Nat.add l.1.val 3)

@[expose] noncomputable def yNets (NT : Nat → Nat) (r : List (Fin 6 × Bool)) : List Nat :=
  r.map fun l => NT (yIdx l)

end CFSG.KC.LyModel

end
