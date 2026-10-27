module

public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.Tactic.LinearCombination

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148T

open Matrix

theorem mulVec_injective_of_unit_fin3 {F : Type*} [Field F] (g : GL (Fin 3) F) :
    Function.Injective (fun v : Fin 3 → F => (g : Matrix (Fin 3) (Fin 3) F) *ᵥ v) := by
  intro v v' h
  have h' := congrArg
    (fun u : Fin 3 → F => ((g⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ u) h
  simpa only [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec] using h'

theorem scalar_mulVec_fin3 {F : Type*} [Field F] (a : F) (u : Fin 3 → F) :
    Matrix.scalar (Fin 3) a *ᵥ u = a • u := by
  ext i
  simp [Matrix.scalar_apply, Matrix.mulVec_diagonal]

theorem zeta_eq_one_of_invariant {F : Type*} [Field F] {y₁ y₂ : GL (Fin 3) F} {ζ : Fˣ}
    (hζ3 : ζ ^ 3 = 1)
    (hζ : y₁ * y₂ * y₁⁻¹ = Matrix.GeneralLinearGroup.scalar (Fin 3) ζ * y₂)
    {W : Submodule F (Fin 3 → F)} (hW0 : W ≠ ⊥) (hWT : W ≠ ⊤)
    (h₁ : ∀ w ∈ W, (y₁ : Matrix (Fin 3) (Fin 3) F) *ᵥ w ∈ W)
    (h₂ : ∀ w ∈ W, (y₂ : Matrix (Fin 3) (Fin 3) F) *ᵥ w ∈ W) : ζ = 1 := by
  have hGL : y₁ * y₂ = Matrix.GeneralLinearGroup.scalar (Fin 3) ζ * (y₂ * y₁) := by
    calc y₁ * y₂ = y₁ * y₂ * y₁⁻¹ * y₁ := by simp
      _ = Matrix.GeneralLinearGroup.scalar (Fin 3) ζ * y₂ * y₁ := by rw [hζ]
      _ = Matrix.GeneralLinearGroup.scalar (Fin 3) ζ * (y₂ * y₁) := by simp only [mul_assoc]
  have hmat : (y₁ : Matrix (Fin 3) (Fin 3) F) * (y₂ : Matrix (Fin 3) (Fin 3) F) =
      Matrix.scalar (Fin 3) (ζ : F) *
        ((y₂ : Matrix (Fin 3) (Fin 3) F) * (y₁ : Matrix (Fin 3) (Fin 3) F)) := by
    have h := congrArg Units.val hGL
    simp only [Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar] at h
    exact h
  have hcomm : ∀ v : Fin 3 → F,
      (y₁ : Matrix (Fin 3) (Fin 3) F) *ᵥ ((y₂ : Matrix (Fin 3) (Fin 3) F) *ᵥ v) =
        (ζ : F) •
          ((y₂ : Matrix (Fin 3) (Fin 3) F) *ᵥ ((y₁ : Matrix (Fin 3) (Fin 3) F) *ᵥ v)) := by
    intro v
    calc (y₁ : Matrix (Fin 3) (Fin 3) F) *ᵥ ((y₂ : Matrix (Fin 3) (Fin 3) F) *ᵥ v)
        = ((y₁ : Matrix (Fin 3) (Fin 3) F) * (y₂ : Matrix (Fin 3) (Fin 3) F)) *ᵥ v :=
          Matrix.mulVec_mulVec v _ _
      _ = (Matrix.scalar (Fin 3) (ζ : F) *
            ((y₂ : Matrix (Fin 3) (Fin 3) F) * (y₁ : Matrix (Fin 3) (Fin 3) F))) *ᵥ v := by
          rw [hmat]
      _ = Matrix.scalar (Fin 3) (ζ : F) *ᵥ
            ((y₂ : Matrix (Fin 3) (Fin 3) F) *ᵥ ((y₁ : Matrix (Fin 3) (Fin 3) F) *ᵥ v)) := by
          rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
      _ = (ζ : F) •
            ((y₂ : Matrix (Fin 3) (Fin 3) F) *ᵥ ((y₁ : Matrix (Fin 3) (Fin 3) F) *ᵥ v)) :=
          scalar_mulVec_fin3 _ _
  have h₁' : ∀ w ∈ W, Matrix.mulVecLin (y₁ : Matrix (Fin 3) (Fin 3) F) w ∈ W :=
    fun w hw => h₁ w hw
  have h₂' : ∀ w ∈ W, Matrix.mulVecLin (y₂ : Matrix (Fin 3) (Fin 3) F) w ∈ W :=
    fun w hw => h₂ w hw
  obtain ⟨fA, hfA⟩ : ∃ f : W →ₗ[F] W, ∀ w : W,
      (f w : Fin 3 → F) = (y₁ : Matrix (Fin 3) (Fin 3) F) *ᵥ (w : Fin 3 → F) :=
    ⟨(Matrix.mulVecLin (y₁ : Matrix (Fin 3) (Fin 3) F)).restrict h₁', fun _ => rfl⟩
  obtain ⟨fB, hfB⟩ : ∃ f : W →ₗ[F] W, ∀ w : W,
      (f w : Fin 3 → F) = (y₂ : Matrix (Fin 3) (Fin 3) F) *ᵥ (w : Fin 3 → F) :=
    ⟨(Matrix.mulVecLin (y₂ : Matrix (Fin 3) (Fin 3) F)).restrict h₂', fun _ => rfl⟩
  have hcomm' : fA * fB = (ζ : F) • (fB * fA) := by
    apply LinearMap.ext
    intro w
    apply Subtype.ext
    simp only [Module.End.mul_apply, LinearMap.smul_apply, Submodule.coe_smul, hfA, hfB]
    exact hcomm _
  have hdet : LinearMap.det fA * LinearMap.det fB =
      (ζ : F) ^ Module.finrank F W * (LinearMap.det fB * LinearMap.det fA) := by
    have h : LinearMap.det (fA * fB) = LinearMap.det ((ζ : F) • (fB * fA)) := by
      rw [hcomm']
    rw [map_mul, LinearMap.det_smul, map_mul] at h
    exact h
  have hinjA : Function.Injective fA := by
    intro w w' h
    apply Subtype.ext
    have h' := congrArg Subtype.val h
    rw [hfA, hfA] at h'
    exact mulVec_injective_of_unit_fin3 y₁ h'
  have hinjB : Function.Injective fB := by
    intro w w' h
    apply Subtype.ext
    have h' := congrArg Subtype.val h
    rw [hfB, hfB] at h'
    exact mulVec_injective_of_unit_fin3 y₂ h'
  have hA0 : LinearMap.det fA ≠ 0 := fun h0 =>
    LinearMap.det_eq_zero_iff_ker_ne_bot.mp h0 (LinearMap.ker_eq_bot.mpr hinjA)
  have hB0 : LinearMap.det fB ≠ 0 := fun h0 =>
    LinearMap.det_eq_zero_iff_ker_ne_bot.mp h0 (LinearMap.ker_eq_bot.mpr hinjB)
  have hAB : LinearMap.det fA * LinearMap.det fB ≠ 0 := mul_ne_zero hA0 hB0
  have hpow : (ζ : F) ^ Module.finrank F W = 1 := by
    have h2 : (ζ : F) ^ Module.finrank F W * (LinearMap.det fA * LinearMap.det fB) =
        1 * (LinearMap.det fA * LinearMap.det fB) := by
      linear_combination -hdet
    exact mul_right_cancel₀ hAB h2
  have hd0 : 0 < Module.finrank F W := by
    have h := Submodule.finrank_lt_finrank_of_lt (bot_lt_iff_ne_bot.mpr hW0)
    rwa [finrank_bot] at h
  have hd3 : Module.finrank F W < 3 := by
    have h := Submodule.finrank_lt hWT
    rwa [Module.finrank_fin_fun] at h
  have hd : Module.finrank F W = 1 ∨ Module.finrank F W = 2 := by omega
  have hζF : (ζ : F) = 1 := by
    rcases hd with hd | hd
    · rw [hd, pow_one] at hpow
      exact hpow
    · rw [hd] at hpow
      have h3 : (ζ : F) ^ 3 = 1 := by
        have h := congrArg Units.val hζ3
        simpa using h
      linear_combination h3 - (ζ : F) * hpow
  apply Units.ext
  simpa using hζF

end CFSG.RankThree.PartTwo.Sec14.Ronan148T
