module

public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagElation

import CFSG.Adapters.SpecialLinearPerfect
import CFSG.LocalAnalysis.StandardType.GGInnerDiagBridgeTypeA

public section

namespace CFSG.StandardType.KGCentPSL

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

theorem exists_pslAutHom_of_ker_le_center {K : Type} [Field K] [Finite K] {n : ℕ} (hn : 3 ≤ n)
    {G : Type} [Group G] (ψ : SpecialLinearGroup (Fin n) K →* G)
    (hker : ψ.ker ≤ Subgroup.center (SpecialLinearGroup (Fin n) K)) :
    ∃ Φ : Subgroup.normalizer (ψ.range : Set G) →* MulAut (projectiveSL n K),
      (∀ (t : Subgroup.normalizer (ψ.range : Set G)) (u u' : SpecialLinearGroup (Fin n) K),
        ψ u' = (t : G) * ψ u * (t : G)⁻¹ → Φ t (proj n K u) = proj n K u') ∧
      ∀ t : Subgroup.normalizer (ψ.range : Set G), Φ t = 1 →
        ∀ g ∈ ψ.range, ∀ h ∈ ψ.range, Commute ((t : G) * g * (t : G)⁻¹ * g⁻¹) h := by
  have hperf : commutator (SpecialLinearGroup (Fin n) K) = ⊤ :=
    CFSG.ClassicalModels.specialLinear_commutator_eq_top_of_three_le hn
  let q₁ : SpecialLinearGroup (Fin n) K →* ↥ψ.range ⧸ Subgroup.center ↥ψ.range :=
    (QuotientGroup.mk' _).comp ψ.rangeRestrict
  have hq₁ : Function.Surjective q₁ :=
    (QuotientGroup.mk'_surjective _).comp ψ.rangeRestrict_surjective
  have hk₁ : q₁.ker = scalars n K := by
    rw [scalars_eq_center]
    ext u
    rw [MonoidHom.mem_ker]
    show (QuotientGroup.mk (ψ.rangeRestrict u) : ↥ψ.range ⧸ Subgroup.center ↥ψ.range) = 1 ↔ _
    rw [QuotientGroup.eq_one_iff]
    refine ⟨InnerDiagA.mem_center_of_rangeRestrict_mem_center hperf ψ hker, fun hu => ?_⟩
    rw [Subgroup.mem_center_iff]
    intro l
    obtain ⟨s, rfl⟩ := ψ.rangeRestrict_surjective l
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hu s]
  let θ : ↥ψ.range ⧸ Subgroup.center ↥ψ.range ≃* projectiveSL n K :=
    (QuotientGroup.quotientKerEquivOfSurjective q₁ hq₁).symm.trans
      (QuotientGroup.quotientMulEquivOfEq hk₁)
  have hθ : ∀ u, θ (q₁ u) = proj n K u := fun u => by
    have h1 : (QuotientGroup.quotientKerEquivOfSurjective q₁ hq₁).symm (q₁ u) =
        (u : SpecialLinearGroup (Fin n) K ⧸ q₁.ker) :=
      (MulEquiv.symm_apply_eq _).mpr rfl
    simp only [θ, MulEquiv.trans_apply, h1, QuotientGroup.quotientMulEquivOfEq_mk]
    rfl
  let ρ : Subgroup.normalizer (ψ.range : Set G) →*
      MulAut (↥ψ.range ⧸ Subgroup.center ↥ψ.range) :=
    { toFun := fun t => QuotientGroup.congr _ _ (ψ.range.normalizerMonoidHom t)
        (Subgroup.map_center_eq (ψ.range.normalizerMonoidHom t))
      map_one' := by
        refine MulEquiv.ext fun q => ?_
        refine QuotientGroup.induction_on q fun x => ?_
        show QuotientGroup.mk (ψ.range.normalizerMonoidHom 1 x) = QuotientGroup.mk x
        rw [map_one]
        rfl
      map_mul' := fun t t' => by
        refine MulEquiv.ext fun q => ?_
        refine QuotientGroup.induction_on q fun x => ?_
        show QuotientGroup.mk (ψ.range.normalizerMonoidHom (t * t') x) =
          QuotientGroup.mk (ψ.range.normalizerMonoidHom t (ψ.range.normalizerMonoidHom t' x))
        rw [map_mul]
        rfl }
  refine ⟨(MulAut.congr θ).toMonoidHom.comp ρ, ?_, ?_⟩
  · intro t u u' h
    have hq : ρ t (q₁ u) = q₁ u' := by
      show QuotientGroup.mk (ψ.range.normalizerMonoidHom t (ψ.rangeRestrict u)) =
        QuotientGroup.mk (ψ.rangeRestrict u')
      congr 1
      exact Subtype.ext h.symm
    show θ (ρ t (θ.symm (proj n K u))) = proj n K u'
    rw [θ.symm_apply_eq.2 (hθ u).symm, hq, hθ]
  · intro t ht g hg h hh
    have h1 : ρ t = 1 :=
      (MulAut.congr θ).injective (by rw [map_one]; exact ht)
    let x : ↥ψ.range := ⟨g, hg⟩
    have h3 : (QuotientGroup.mk (ψ.range.normalizerMonoidHom t x) :
        ↥ψ.range ⧸ Subgroup.center ↥ψ.range) = QuotientGroup.mk x :=
      DFunLike.congr_fun h1 (QuotientGroup.mk x)
    have h2 : (QuotientGroup.mk (ψ.range.normalizerMonoidHom t x * x⁻¹) :
        ↥ψ.range ⧸ Subgroup.center ↥ψ.range) = 1 := by
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, h3, mul_inv_cancel]
    have h6 := Subgroup.mem_center_iff.1 ((QuotientGroup.eq_one_iff _).1 h2) ⟨h, hh⟩
    exact (congrArg Subtype.val h6).symm

end CFSG.StandardType.KGCentPSL

end
