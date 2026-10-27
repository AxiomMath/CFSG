module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DefsModule
public import CFSG.Adapters.ProjectiveSpecialLinear

@[expose] public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22 Subgroup

@[expose] def W4Lem3_3J2 : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
    ∀ Y L : Subgroup (MulAut W),
      L ≤ Y → (L.subgroupOf Y).Normal → Fstar Y = L → IsSpor ↥L .J2 →
      IsIrrOn L ⊤ ⊥ → rk W = 12 →
      (∃ z ∈ L, orderOf z = 2 ∧ rk (commSub (⊤ : Subgroup W) (Subgroup.zpowers z)) = 4) ∧
        E3.aParam Y ≤ 2

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

end
