module

public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.LinearAlgebra.Matrix.Transvection
public import CFSG.LieType.Universal.Unitary.Basic

public section

namespace CFSG.StandardType

namespace UnitaryAlg

open Matrix CFSG.LieType.Universal.Unitary

section Extension

variable {F : Type} [Field F]

theorem exists_ringEquiv_extension (σ : F ≃+* F) :
    ∃ σ' : AlgebraicClosure F ≃+* AlgebraicClosure F,
      ∀ x : F, σ' (algebraMap F (AlgebraicClosure F) x) = algebraMap F (AlgebraicClosure F) (σ x) :=
  ⟨IsAlgClosure.equivOfEquiv (AlgebraicClosure F) (AlgebraicClosure F) σ,
    fun x => IsAlgClosure.equivOfEquiv_algebraMap (AlgebraicClosure F) (AlgebraicClosure F) σ x⟩

theorem map_algebraMap_injective {ι : Type*} :
    Function.Injective fun M : Matrix ι ι F => M.map (algebraMap F (AlgebraicClosure F)) :=
  Matrix.map_injective (algebraMap F (AlgebraicClosure F)).injective

end Extension

section CubeRoots

variable {K : Type*} [Field K]

theorem eq_one_or_eq_or_eq_sq_of_pow_three {ζ : K} (hζ1 : ζ ≠ 1) (hζ3 : ζ ^ 3 = 1) {η : K}
    (hη : η ^ 3 = 1) : η = 1 ∨ η = ζ ∨ η = ζ ^ 2 := by
  have hz : ζ ^ 2 + ζ + 1 = 0 := by
    have h : (ζ - 1) * (ζ ^ 2 + ζ + 1) = 0 := by
      have : (ζ - 1) * (ζ ^ 2 + ζ + 1) = ζ ^ 3 - 1 := by ring
      rw [this, hζ3, sub_self]
    rcases mul_eq_zero.mp h with h1 | h1
    · exact absurd (sub_eq_zero.mp h1) hζ1
    · exact h1
  have hprod : (η - 1) * (η - ζ) * (η - ζ ^ 2) = 0 := by
    have : (η - 1) * (η - ζ) * (η - ζ ^ 2)
        = η ^ 3 - 1 - (ζ ^ 2 + ζ + 1) * (η ^ 2 - η) + (ζ ^ 3 - 1) * (η - 1) := by ring
    rw [this, hz, hζ3, hη]
    ring
  rcases mul_eq_zero.mp hprod with h | h
  · rcases mul_eq_zero.mp h with h1 | h1
    · exact Or.inl (sub_eq_zero.mp h1)
    · exact Or.inr (Or.inl (sub_eq_zero.mp h1))
  · exact Or.inr (Or.inr (sub_eq_zero.mp h))

variable {F : Type} [Field F]

theorem apply_eq_inv_of_pow_three {σ : F ≃+* F} {σ' : AlgebraicClosure F ≃+* AlgebraicClosure F}
    (hσ' : ∀ x : F, σ' (algebraMap F (AlgebraicClosure F) x) =
      algebraMap F (AlgebraicClosure F) (σ x))
    {ζ : F} (hζ1 : ζ ≠ 1) (hζ3 : ζ ^ 3 = 1) (hσζ : σ ζ = ζ⁻¹) {η : AlgebraicClosure F}
    (hη : η ^ 3 = 1) : σ' η = η⁻¹ := by
  let ι : F →+* AlgebraicClosure F := algebraMap F (AlgebraicClosure F)
  have hιζ1 : ι ζ ≠ 1 := fun h => hζ1 (ι.injective (by simpa using h))
  have hιζ3 : (ι ζ) ^ 3 = 1 := by rw [← map_pow, hζ3, map_one]
  rcases eq_one_or_eq_or_eq_sq_of_pow_three hιζ1 hιζ3 hη with h | h | h
  · rw [h]; simp
  · rw [h, hσ', hσζ, map_inv₀]
  · rw [h]
    have hc' : σ' (ι ζ) = (ι ζ)⁻¹ := by rw [hσ', hσζ, map_inv₀]
    rw [map_pow, hc', inv_pow]

theorem apply_eq_self_of_pow_three {σ : F ≃+* F} {σ' : AlgebraicClosure F ≃+* AlgebraicClosure F}
    (hσ' : ∀ x : F, σ' (algebraMap F (AlgebraicClosure F) x) =
      algebraMap F (AlgebraicClosure F) (σ x))
    {ζ : F} (hζ1 : ζ ≠ 1) (hζ3 : ζ ^ 3 = 1) (hσζ : σ ζ = ζ) {η : AlgebraicClosure F}
    (hη : η ^ 3 = 1) : σ' η = η := by
  let ι : F →+* AlgebraicClosure F := algebraMap F (AlgebraicClosure F)
  have hιζ1 : ι ζ ≠ 1 := fun h => hζ1 (ι.injective (by simpa using h))
  have hιζ3 : (ι ζ) ^ 3 = 1 := by rw [← map_pow, hζ3, map_one]
  rcases eq_one_or_eq_or_eq_sq_of_pow_three hιζ1 hιζ3 hη with h | h | h
  · rw [h]; simp
  · rw [h, hσ', hσζ]
  · rw [h]
    have hc' : σ' (ι ζ) = ι ζ := by rw [hσ', hσζ]
    rw [map_pow, hc']

end CubeRoots

section Antidiag

variable {F : Type} [Field F] {n : ℕ}

theorem transpose_antidiag : (antidiag n : Matrix (Fin n) (Fin n) F)ᵀ = antidiag n := by
  ext i j
  simp only [transpose_apply, antidiag, of_apply]
  by_cases h : j = Fin.rev i
  · have hi : i = Fin.rev j := by rw [h, Fin.rev_rev]
    rw [if_pos hi, if_pos h]
  · have hi : i ≠ Fin.rev j := fun hh => h (by rw [hh, Fin.rev_rev])
    rw [if_neg hi, if_neg h]

theorem isUnit_antidiag : IsUnit (antidiag n : Matrix (Fin n) (Fin n) F) := by
  have hmul : (antidiag n : Matrix (Fin n) (Fin n) F) * antidiag n = 1 := by
    ext i j
    rw [Matrix.mul_apply]
    simp only [antidiag, of_apply, Matrix.one_apply]
    rw [Finset.sum_eq_single (Fin.rev i)
      (fun b _ hb => by simp [hb])
      (fun h => absurd (Finset.mem_univ _) h)]
    rw [Fin.rev_rev]
    simp [eq_comm]
  exact isUnit_iff_exists.mpr ⟨antidiag n, hmul, hmul⟩

theorem transpose_form_of_conjTr (σ : F ≃+* F) {A : Matrix (Fin n) (Fin n) F}
    (h : conjTr σ A * antidiag n * A = antidiag n) : Aᵀ * antidiag n * A.map σ = antidiag n := by
  have h' := congrArg Matrix.transpose h
  simp only [conjTr, Matrix.transpose_mul, Matrix.transpose_transpose, transpose_antidiag] at h'
  simpa [Matrix.mul_assoc] using h'

end Antidiag

end UnitaryAlg

end CFSG.StandardType
