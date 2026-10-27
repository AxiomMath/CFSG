module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2NormalizerFittingActionCommon
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

noncomputable section
namespace CFSG.GorensteinWalter

universe u

/-! ## Lifting innerness from the central quotient of the layer -/

/-- If every element of `F(U) ⊓ N_G(X)` acts on the central quotient of
the normalizer layer as conjugation by an element of that layer, then it
acts by that same inner automorphism on the layer itself.  Perfectness of
the component layer kills the central discrepancy.

This is the exact lifting step between a semilinear PSL-range conclusion
and `secondCase_psl2_normalizer_innerAction`. -/
public theorem secondCase_psl2_normalizer_innerAction_of_quotientInner
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) (X : Subgroup G)
    (hquot :
      let N : Subgroup G := Subgroup.normalizer (X : Set G)
      let L : Subgroup G := componentLayerOf N
      ∀ p, (hp : p ∈ c.FU ⊓ N) →
        ∃ ℓ : L, ∀ x : L,
          QuotientGroup.mk' (Subgroup.center L)
              (⟨p * (x : G) * p⁻¹,
                (componentLayerOf_isNormalIn N).2 p hp.2 (x : G) x.2⟩ : L) =
            QuotientGroup.mk' (Subgroup.center L)
              (ℓ * x * ℓ⁻¹)) :
    secondCase_psl2_normalizer_innerAction c X := by
  classical
  let N : Subgroup G := Subgroup.normalizer (X : Set G)
  let L : Subgroup G := componentLayerOf N
  have hLnorm : IsNormalIn L N := componentLayerOf_isNormalIn N
  have hLperf : Group.IsPerfect L := componentLayerOf_isPerfect N
  intro p hp
  obtain ⟨ℓ, hq⟩ := hquot p hp
  have hℓN : (ℓ : G) ∈ N := hLnorm.1 ℓ.2
  let α : L ≃* L := conjOnSubgroupEquiv N L p hp.2 hLnorm
  let β : L ≃* L := conjOnSubgroupEquiv N L (ℓ : G) hℓN hLnorm
  have hdelta : ∀ x : L, α x * (β x)⁻¹ ∈ Subgroup.center L := by
    intro x
    have hqeq := hq x
    have hqeq' : QuotientGroup.mk' (Subgroup.center L) (α x) =
        QuotientGroup.mk' (Subgroup.center L) (β x) := by
      change QuotientGroup.mk' (Subgroup.center L)
          ⟨p * (x : G) * p⁻¹, hLnorm.2 p hp.2 (x : G) x.2⟩ =
        QuotientGroup.mk' (Subgroup.center L)
          ⟨(ℓ : G) * (x : G) * (ℓ : G)⁻¹,
            hLnorm.2 (ℓ : G) hℓN (x : G) x.2⟩
      convert hqeq using 1
      all_goals
        apply congrArg (QuotientGroup.mk' (Subgroup.center L))
        apply Subtype.ext
        rfl
    have hqone : QuotientGroup.mk' (Subgroup.center L) (α x * (β x)⁻¹) = 1 := by
      rw [map_mul, map_inv, hqeq']
      simp
    exact (QuotientGroup.eq_one_iff (N := Subgroup.center L)
      (α x * (β x)⁻¹)).mp hqone
  have hab : α = β := perfect_central_automorphism_eq hLperf α β hdelta
  refine ⟨(ℓ : G), ℓ.2, ?_⟩
  intro x hx
  have heq := congrArg (fun a : L ≃* L => a ⟨x, hx⟩) hab
  exact congrArg Subtype.val heq

end CFSG.GorensteinWalter
