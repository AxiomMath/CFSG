module

public import CFSG.ClassicalGroups.Unitary.Elements
public import CFSG.RankThree.GF2n.Smith81.S81A5Basic

public section

namespace CFSG.RankThree.GF2n.Smith81.U6Cube

open CFSG.RankThree.GF2n.Smith81.A5Cube Matrix CFSG.LieType.Universal.Unitary
  CFSG.ClassicalGroups.Unitary

variable {K : Type*} [Field K] {σ : K ≃+* K}

theorem conj_tvMat {n : ℕ} (hσ : ∀ c, σ (σ c) = c) (g : SUid σ n) (a : Fin n → K) (c : K) :
    ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * tvMat σ a c *
        (((g : GL (Fin n) K)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      tvMat σ ((g : GL (Fin n) K).val.mulVec a) c := by
  have hu : conjTr σ ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 := (mem_SUid.mp g.2).2
  have hinv : (((g : GL (Fin n) K)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      conjTr σ ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
    rw [Matrix.coe_units_inv]
    exact Matrix.inv_eq_left_inv hu
  have hgg : ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      conjTr σ ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 := by
    rw [← hinv, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hf : (fun i => σ (a i)) ᵥ* conjTr σ ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      fun j => σ ((g : GL (Fin n) K).val.mulVec a j) := by
    funext j
    simp only [vecMul, dotProduct, conjTr, Matrix.map_apply, Matrix.transpose_apply,
      Matrix.mulVec, map_sum, map_mul]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  rw [hinv, tvMat, Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul, Matrix.add_mul,
    Matrix.smul_mul, hgg, Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, hf, tvMat]

end CFSG.RankThree.GF2n.Smith81.U6Cube
