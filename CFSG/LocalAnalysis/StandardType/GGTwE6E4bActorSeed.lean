module

public import CFSG.LocalAnalysis.StandardType.GGTwE6ConnectedReflection

public noncomputable section

namespace CFSG.StandardType.E4bActorSeed

open Subgroup CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.StandardType.NoOffTwE6Three CFSG.RankThree.Classical2
  CFSG.RankThree.PartOne.KE CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.HardMathSupport.Lang.E6Descent CFSG.LieType.AlgebraicGroups
  CFSG.StandardType.SCFourCover

theorem conj_of_inverted_cube {J : Type} [Group J]
    (τ : MulAut J) (hτ : τ ^ 3 = 1) (g : J)
    (hinv : MulAut.conj g * τ * (MulAut.conj g)⁻¹ = τ⁻¹) :
    MulAut.conj (g * (τ g)⁻¹) = τ := by
  have hc : MulAut.conj (g * (τ g)⁻¹) =
      MulAut.conj g * τ * (MulAut.conj g)⁻¹ * τ⁻¹ := by
    ext x
    change (g * (τ g)⁻¹) * x * (g * (τ g)⁻¹)⁻¹ =
      g * τ (g⁻¹ * τ.symm x * g) * g⁻¹
    simp only [map_mul, map_inv, τ.apply_symm_apply]
    group
  have h2 : τ * τ = τ⁻¹ := eq_inv_iff_mul_eq_one.mpr (by
    simpa only [pow_succ, pow_zero, one_mul, mul_assoc] using hτ)
  calc
    MulAut.conj (g * (τ g)⁻¹) = τ⁻¹ * τ⁻¹ := by rw [hc, hinv]
    _ = (τ * τ) * τ⁻¹ := by rw [h2]
    _ = τ := by group

variable {n : ℕ} (hn : 1 ≤ n) {K : Type} [Field K] [Finite K]
  (hK : Nat.card K = (2 ^ n) ^ 2) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ 2 ^ n)
  {Ω : Type} [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
  (Fr : Ω →+* Ω) (hFr : ∀ c, Fr c = c ^ 2 ^ n)
  (ε : ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom) ≃* TwE6Delta.RecipeR K n)
  (hε : ∀ x : MulAut ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom),
    MulAut.congr ε x ∈ TwE6Delta.RecipeI K n ↔ x ∈ (RecipeExcLang.twConj K σ).range)
  {J : Type} [Group J] {ψ : J →* TwE6Delta.RecipeR K n}
  (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ center J) (hperf : commutator J = ⊤)
  {A : Subgroup (MulAut J)}
  (hAI : ∀ a ∈ A, ∃ φ ∈ TwE6Delta.RecipeI K n, ∀ j, φ (ψ j) = ψ (a j))

theorem recipeActorModelEquiv_conj_recipeMatrix (a : A) (j : J) :
    (recipeActorModelEquiv hn hK σ hσ Fr hFr ε hε hψ hker hperf hAI a : ModGL .E6 Ω) *
        recipeMatrixHom σ ε (ψ := ψ) j *
      (recipeActorModelEquiv hn hK σ hσ Fr hFr ε hε hψ hker hperf hAI a : ModGL .E6 Ω)⁻¹ =
        recipeMatrixHom σ ε (ψ := ψ) (a.1 j) := by
  let γ := recipeActorModelEquiv hn hK σ hσ Fr hFr ε hε hψ hker hperf hAI
  let r : TwistedDiag.Rgrp Ω Fr :=
    ⟨γ a, rgrpModel_le_Rgrp hn hK σ hσ Fr hFr ε _ (γ a).2⟩
  have heval : rgrpRecipeAut hn hK σ hσ Fr hFr ε r (ψ j) = ψ (a.1 j) :=
    recipeActorModelEquiv_apply hn hK σ hσ Fr hFr ε hε hψ hker hperf hAI a j
  have hr := rgrpRecipeAut_apply hn hK σ hσ Fr hFr ε r (ε.symm (ψ j))
  rw [ε.apply_symm_apply, heval] at hr
  have hc : rgrpConjAut hn hK σ hσ Fr hFr r (ε.symm (ψ j)) =
      ε.symm (ψ (a.1 j)) := by
    apply ε.injective
    rw [ε.apply_symm_apply]
    exact hr.symm
  have hm := congrArg (fun z : ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom) =>
    baseChangeGL (τ := Tag.E6) (algebraMap K Ω) z.1) hc
  rw [baseChange_rgrpConjAut] at hm
  exact hm

end CFSG.StandardType.E4bActorSeed
