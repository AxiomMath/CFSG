module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2NormalizerFittingActionCommon
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

noncomputable section
namespace CFSG.GorensteinWalter

universe u

/-! ## Normalizer-layer packaging

This bridge keeps the model-dependent part of Fact 1.10(ii) separate from
the ambient normalizer notation.  It is useful when a PSL₂/PΓL₂ argument has
already produced the pointwise inner representative on the actual layer.
-/

public theorem secondCase_psl2_normalizer_innerAction_of_layer
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) (X : Subgroup G)
    (L : Subgroup G)
    (hLayer : componentLayerOf (Subgroup.normalizer (X : Set G)) = L)
    (hpoint : ∀ p ∈ (c.FU ⊓ Subgroup.normalizer (X : Set G)),
      ∃ ℓ ∈ L, ∀ x ∈ L,
        p * x * p⁻¹ = ℓ * x * ℓ⁻¹) :
    secondCase_psl2_normalizer_innerAction c X := by
  intro p hp
  rw [hLayer]
  exact hpoint p hp

end CFSG.GorensteinWalter
