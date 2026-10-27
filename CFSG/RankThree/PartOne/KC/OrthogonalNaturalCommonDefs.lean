module

public import CFSG.RankThree.PartOne.KC.OrthogonalSupportedScalarConj

public section

namespace CFSG.RankThree.PartOne.KCOrthogonal

open Module QuadraticMap CFSG.RankThree.Classical2 CFSG.ClassicalGroups.Orthogonal

section Semilin

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}
  (F : V ≃+ V) (σ : K ≃+* K) (hF : ∀ (c : K) (v : V), F (c • v) = σ c • F v)

theorem semilinConj_injective : Function.Injective (semilinConj F σ hF) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  refine LinearEquiv.ext fun v => ?_
  have h1 := DFunLike.congr_fun hg (F v)
  rw [semilinConj_apply, AddEquiv.symm_apply_apply] at h1
  exact F.injective h1

variable (μ : K) (hFQ : ∀ v, Q (F v) = μ * σ (Q v))

@[expose] noncomputable def semilinOrth : orthDerived Q →* orthDerived Q :=
  ((semilinConj F σ hF).comp (orthDerived Q).subtype).codRestrict (orthDerived Q) fun g =>
    semilinConj_mem_orthDerived F σ hF μ hFQ g.2

theorem semilinOrth_apply (g : orthDerived Q) :
    ((semilinOrth F σ hF μ hFQ g : orthDerived Q) : V ≃ₗ[K] V) = semilinConj F σ hF g :=
  rfl

theorem semilinOrth_injective : Function.Injective (semilinOrth F σ hF μ hFQ) := fun _ _ h =>
  Subtype.ext (semilinConj_injective F σ hF (congrArg Subtype.val h))

variable [Finite K] [FiniteDimensional K V]

theorem semilinOrth_surjective : Function.Surjective (semilinOrth F σ hF μ hFQ) := by
  have : Finite V := Module.finite_of_finite K
  have : Finite (V ≃ₗ[K] V) :=
    Finite.of_injective (fun e : V ≃ₗ[K] V => (e : V → V)) fun e₁ e₂ h =>
      LinearEquiv.ext (congrFun h)
  exact Finite.surjective_of_injective (semilinOrth_injective F σ hF μ hFQ)

end Semilin

end CFSG.RankThree.PartOne.KCOrthogonal
