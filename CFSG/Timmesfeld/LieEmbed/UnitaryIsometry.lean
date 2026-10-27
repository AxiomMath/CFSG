module

public import CFSG.Timmesfeld.LieEmbed.UnitaryForms

public section

namespace CFSG.Timmesfeld.LieEmbed

open Matrix CFSG.LieType.Universal.Unitary

variable {F : Type*} [Field F] {σ : F ≃+* F} {n : ℕ}

theorem uRow_mulVec_vecMul_of_isometry {A : Matrix (Fin n) (Fin n) F}
    (hA : conjTr σ A * antidiag n * A = antidiag n) (v : Fin n → F) :
    uRow σ (A *ᵥ v) ᵥ* A = uRow σ v := by
  rw [conjTr] at hA
  rw [uRow, uRow, map_mulVec_sigma, vecMul_mulVec, vecMul_vecMul, hA]

theorem mul_uNil_of_isometry {A : Matrix (Fin n) (Fin n) F}
    (hA : conjTr σ A * antidiag n * A = antidiag n) (v : Fin n → F) :
    A * uNil σ v = uNil σ (A *ᵥ v) * A := by
  rw [uNil, uNil, mul_vecMulVec, vecMulVec_mul, uRow_mulVec_vecMul_of_isometry hA]

theorem mul_uTrans_of_isometry {A : Matrix (Fin n) (Fin n) F}
    (hA : conjTr σ A * antidiag n * A = antidiag n) (v : Fin n → F) (c : F) :
    A * uTrans σ v c = uTrans σ (A *ᵥ v) c * A := by
  rw [uTrans, uTrans, Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul, Matrix.add_mul,
    Matrix.one_mul, Matrix.smul_mul, mul_uNil_of_isometry hA]

theorem map_uTrans (φ : F ≃+* F) (hφ : ∀ c, φ (σ c) = σ (φ c)) (v : Fin n → F) (c : F) :
    (uTrans σ v c).map φ = uTrans σ (fun i => φ (v i)) (φ c) := by
  rw [uTrans, uTrans, Matrix.map_add _ (map_add φ), Matrix.map_one _ (map_zero φ) (map_one φ),
    Matrix.map_smul' _ _ _ (map_mul φ)]
  congr 2
  ext i j
  simp only [uNil, Matrix.map_apply, vecMulVec_apply, uRow_apply, map_mul, hφ]

end CFSG.Timmesfeld.LieEmbed
