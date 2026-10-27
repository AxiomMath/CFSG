module

public import CFSG.Quasithin.Vol2.Ch11SecSObl

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecS

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13

@[expose] def Obl11_1_2StarShapeJ4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I V₁ V₂ X K K₀ I₀ : Subgroup G),
    StarHyp G T L I V₁ V₂ X K → IsK0 T L V₁ K K₀ →
    pCoreOf 2 (K₀ ⊔ LOf L V₂ ⊔ X ⊔ T) ≠ ⊥ →
    quasithinIsCComponent I₀ (K₀ ⊔ LOf L V₂ ⊔ X ⊔ T) →
    T ≤ Subgroup.normalizer (I₀ : Set G) → K₀ ≤ I₀ → LOf L V₂ ≤ I₀ → X ≤ I₀ →
      ¬ IsSporadic .J4 (↥I₀ ⧸ CFSG.pCore 2 ↥I₀)

end CFSG.Quasithin.Vol2.Ch11.SecS
