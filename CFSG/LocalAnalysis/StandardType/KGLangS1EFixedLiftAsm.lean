module

public import CFSG.LocalAnalysis.StandardType.KGLangS1EFixedLiftCore
public import CFSG.LocalAnalysis.StandardType.GGNbrLangKGInputs
public import CFSG.LocalAnalysis.StandardType.GGL45NtExcBridgeDefs

public section

set_option linter.unusedSectionVars false

namespace CFSG.StandardType

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Minuscule
  CFSG.LieType.Steinberg.Isogeny CFSG.HardMathSupport.C14Exc


private lemma kgLangS1EFixedLiftAux_kgInducedAut_apply_mk {K R : Type*} [Group K] [Group R]
    (θ : K ⧸ Subgroup.center K ≃* R) (α : MulAut K) (k : K) :
    kgInducedAut θ α (θ (QuotientGroup.mk k)) = θ (QuotientGroup.mk (α k)) := by
  change (MulAut.congr θ) ((centerQuotAut K) α) (θ (QuotientGroup.mk k)) =
    θ (QuotientGroup.mk (α k))
  rw [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply,
    MulEquiv.symm_apply_apply]
  rfl

theorem kgLangS1EFixedLift_assembly (k : Type) [Field k] [Finite k] (L : Type) [Field L]
    [CharP L 2] [Algebra k L] [Algebra.IsAlgebraic k L] (R : Type) [Group R]
    (ρ₀ : R →* ModGL Tag.E6 k) (F₀ : ModGL Tag.E6 L →* ModGL Tag.E6 L)
    (Θ : ↥(ratPts Tag.E6 L (endPow F₀ 3)) →* MulAut R)
    (hconjΘ : ∀ (g : ↥(ratPts Tag.E6 L (endPow F₀ 3))) (r : R),
      baseChangeGL (τ := Tag.E6) (algebraMap k L) (ρ₀ (Θ g r)) =
        (g : ModGL Tag.E6 L) * baseChangeGL (τ := Tag.E6) (algebraMap k L) (ρ₀ r) *
          (g : ModGL Tag.E6 L)⁻¹)
    (K : Type) [Group K] (θ : K ⧸ Subgroup.center K ≃* R)
    {U : Type} [Group U] [Group.IsPerfect U] (j : U →* ↥(e6Data_valid.minGroup k))
    (hj : Function.Injective j) (κ : U →* K) (hκ : Function.Surjective κ)
    (hκρ : ∀ u, ρ₀ (θ (QuotientGroup.mk (κ u))) =
      ((e6Isogeny k (j u) : ↥(adjointGroup Tag.E6 k)) : ModGL Tag.E6 k))
    (α : MulAut K) (αU : MulAut U) (hα : ∀ u, κ (αU u) = α (κ u))
    (g : ↥(ratPts Tag.E6 L (endPow F₀ 3))) (hg : kgInducedAut θ α = Θ g)
    (r : R) (x : K) (hx : θ (QuotientGroup.mk x) = r)
    (hc : ∃ c : ModGL Tag.E6 L, c ∈ adjointGroup Tag.E6 L ∧
      c * (g : ModGL Tag.E6 L) * c⁻¹ ∈ torusGroup Tag.E6 L ∧
      c * baseChangeGL (τ := Tag.E6) (algebraMap k L) (ρ₀ r) * c⁻¹ ∈ torusGroup Tag.E6 L) :
    α x = x := by
  obtain ⟨c, hc, hcg, hcr⟩ := hc
  obtain ⟨u₀, rfl⟩ := hκ x
  subst hx
  have hconj : ∀ u : U,
      baseChangeGL (τ := Tag.E6) (algebraMap k L)
          ((e6Isogeny k (j (αU u)) : ↥(adjointGroup Tag.E6 k)) : ModGL Tag.E6 k) =
        (g : ModGL Tag.E6 L) * baseChangeGL (τ := Tag.E6) (algebraMap k L)
          ((e6Isogeny k (j u) : ↥(adjointGroup Tag.E6 k)) : ModGL Tag.E6 k) *
          (g : ModGL Tag.E6 L)⁻¹ := by
    intro u
    have h1 : Θ g (θ (QuotientGroup.mk (κ u))) = θ (QuotientGroup.mk (κ (αU u))) := by
      rw [← hg, hα u]
      exact kgLangS1EFixedLiftAux_kgInducedAut_apply_mk θ α (κ u)
    have h2 := hconjΘ g (θ (QuotientGroup.mk (κ u)))
    rw [h1, hκρ, hκρ] at h2
    exact h2
  rw [hκρ u₀] at hcr
  have hcore := kgLangS1EFixedLift_core k L j hj αU hc g.2.1 hconj hcg hcr
  calc α (κ u₀) = κ (αU u₀) := (hα u₀).symm
    _ = κ u₀ := by rw [hcore]

end CFSG.StandardType
