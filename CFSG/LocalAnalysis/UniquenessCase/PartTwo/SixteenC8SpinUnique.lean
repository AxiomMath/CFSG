module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup

@[expose] def RSp6SpinUnique : Prop :=
  ∀ (W₁ W₂ : Type) [CommGroup W₁] [CommGroup W₂] [Finite W₁] [Finite W₂],
    (∀ w : W₁, w ^ 2 = 1) → (∀ w : W₂, w ^ 2 = 1) →
    ∀ (H₁ : Subgroup (MulAut W₁)) (H₂ : Subgroup (MulAut W₂)),
      IsSpn ↥H₁ 6 1 → IsSpn ↥H₂ 6 1 →
      rk ↥(⊤ : Subgroup W₁) = 8 → rk ↥(⊤ : Subgroup W₂) = 8 →
      IsIrrOn H₁ ⊤ ⊥ → IsIrrOn H₂ ⊤ ⊥ →
        ∃ (α : ↥H₁ ≃* ↥H₂) (φ : W₁ ≃* W₂),
          ∀ (h : ↥H₁) (w : W₁), φ ((h : MulAut W₁) w) = ((α h : ↥H₂) : MulAut W₂) (φ w)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
