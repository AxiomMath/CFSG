module

public import CFSG.LocalAnalysis.StandardType.GGOneFiveDefs

public section

namespace CFSG.StandardType

@[expose] def GGSecFiveCoxProdInput : Prop :=
  ∀ (ι : Type) (M : CoxeterMatrix ι), GGIsWeylMatrix M →
    (¬ ∃ e : Fin 2 ≃ ι, M = CoxeterMatrix.G₂.reindex e) →
      ∀ (i j : ι) (g h : M.Group),
        orderOf (g * M.simple i * g⁻¹ * (h * M.simple j * h⁻¹)) ≤ 4

end CFSG.StandardType
