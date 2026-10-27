module

public import CFSG.LieType.Universal.Unitary.Basic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK.Insp

open Matrix CFSG.LieType.Universal.Unitary

section Forms

variable {K : Type} [Field K] (σ : K ≃+* K)

theorem conj_isometry {n : ℕ} {P Pi J S Z : Matrix (Fin n) (Fin n) K} (hPPi : P * Pi = 1)
    (hP : conjTr σ P * J * P = S) (hZ : conjTr σ Z * S * Z = S) :
    conjTr σ (P * Z * Pi) * J * (P * Z * Pi) = J := by
  calc conjTr σ (P * Z * Pi) * J * (P * Z * Pi)
      = conjTr σ Pi * (conjTr σ Z * (conjTr σ P * J * P) * Z) * Pi := by
        simp only [conjTr_mul, Matrix.mul_assoc]
    _ = conjTr σ Pi * S * Pi := by rw [hP, hZ]
    _ = conjTr σ Pi * (conjTr σ P * J * P) * Pi := by rw [hP]
    _ = conjTr σ (P * Pi) * J * (P * Pi) := by simp only [conjTr_mul, Matrix.mul_assoc]
    _ = J := by rw [hPPi, conjTr_one, Matrix.one_mul, Matrix.mul_one]

theorem key_isometry {n : ℕ} {B₁ B₂ B₁i J S₀ : Matrix (Fin n) (Fin n) K} (h1 : B₁ * B₁i = 1)
    (hB₁ : conjTr σ B₁ * S₀ * B₁ = J) (hB₂ : conjTr σ B₂ * J * B₂ = J) :
    conjTr σ (B₂ * B₁i) * J * (B₂ * B₁i) = S₀ := by
  calc conjTr σ (B₂ * B₁i) * J * (B₂ * B₁i)
      = conjTr σ B₁i * (conjTr σ B₂ * J * B₂) * B₁i := by
        simp only [conjTr_mul, Matrix.mul_assoc]
    _ = conjTr σ B₁i * J * B₁i := by rw [hB₂]
    _ = conjTr σ B₁i * (conjTr σ B₁ * S₀ * B₁) * B₁i := by rw [hB₁]
    _ = conjTr σ (B₁ * B₁i) * S₀ * (B₁ * B₁i) := by simp only [conjTr_mul, Matrix.mul_assoc]
    _ = S₀ := by rw [h1, conjTr_one, Matrix.one_mul, Matrix.mul_one]

theorem conjTr_antidiag (n : ℕ) :
    conjTr σ (antidiag n : Matrix (Fin n) (Fin n) K) = antidiag n := by
  ext i j
  simp only [conjTr, antidiag, transpose_apply, map_apply, of_apply]
  by_cases h : i = Fin.rev j
  · have h' : j = Fin.rev i := by rw [h, Fin.rev_rev]
    rw [if_pos h, if_pos h', map_one]
  · have h' : ¬ j = Fin.rev i := fun hh => h (by rw [hh, Fin.rev_rev])
    rw [if_neg h, if_neg h', map_zero]

theorem det_antidiag_three : (antidiag 3 : Matrix (Fin 3) (Fin 3) K).det ≠ 0 := by
  have h : (antidiag 3 : Matrix (Fin 3) (Fin 3) K) = !![0, 0, 1; 0, 1, 0; 1, 0, 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [antidiag] <;> decide
  rw [h, Matrix.det_fin_three]
  simp

end Forms

end CFSG.LocalAnalysis.UniquenessCase.UCK.Insp
