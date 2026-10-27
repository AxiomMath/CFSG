module

public import CFSG.Sporadic.Schreier.RuCenters

public noncomputable section

namespace CFSG.Sporadic.RuSchreier

@[expose] def ruXN :
    Subgroup (Equiv.Perm (Fin 4060)) :=
  Subgroup.closure {x | ∃ c ∈ ruC, ∃ a ∈ ruESub, x = c * a * c⁻¹}

@[expose] def ruG5 : Equiv.Perm (Fin 4060) := ruC0 ^ 4

end CFSG.Sporadic.RuSchreier
