module

public import CFSG.Monster.B.Dyadic.PairK
public import CFSG.Monster.B.Max2.Prog

public section

namespace CFSG.Monster.B.Dyadic

@[expose] noncomputable def cK : Matrix (Fin 4370) (Fin 4370) (ZMod 2) := progRegs genA₁ genA₂ 1

@[expose] noncomputable def dK : Matrix (Fin 4370) (Fin 4370) (ZMod 2) := progRegs genA₁ genA₂ 2

@[expose] def FactPinned : Prop :=
  cK * cK = 1 ∧ cK ≠ 1 ∧ dK ^ 48 = 1 ∧ dK ^ 24 ≠ 1 ∧ dK ^ 16 ≠ 1 ∧
    dK ^ 24 * cK = cK * dK ^ 24 ∧ IsUnit TK ∧ genA₂ * genA₂ * genA₂ = 1 ∧
    (dK ^ 24 * (genA₂ * genA₂ * dK ^ 24 * genA₂)) ^ 5 = 1

end CFSG.Monster.B.Dyadic

end
