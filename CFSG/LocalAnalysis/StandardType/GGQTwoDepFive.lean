module

public import CFSG.LocalAnalysis.StandardType.GGQTwoLin

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Module QTwoLin

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def GGQ2HeartInput : Prop :=
  ∀ (D : GGQ2Lin 3) [FiniteDimensional (ZMod 3) D.V] (e : Fin 6 ≃ D.ι),
    D.coxeter = CoxeterMatrix.E₆.reindex e → Module.finrank (ZMod 3) D.V = 5 →
    ∀ (A : Subgroup (D.V ≃ₗ[ZMod 3] D.V)), D.weyl ≤ A → TransvectionFree A →
      ∀ a ∈ A, ∃ g ∈ D.weyl, (∀ v, a v = g v) ∨ (∀ v, a v = -(g v))

end CFSG.StandardType

end
