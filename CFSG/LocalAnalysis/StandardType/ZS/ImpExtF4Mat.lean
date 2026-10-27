module

public import CFSG.LocalAnalysis.StandardType.ZS.ExcMatrices

public section

namespace CFSG.StandardType.ZS.FFourCoord

section Matrices

variable {K : Type} [CommRing K] {n : ℕ}

private theorem vecMulVec_mul_vecMulVec {v w ρ κ : Fin n → K} :
    Matrix.vecMulVec v w * Matrix.vecMulVec ρ κ =
      Matrix.vecMulVec v ((∑ i, w i * ρ i) • κ) := by
  ext i j
  simp only [Matrix.vecMulVec_apply, Matrix.mul_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun x _ => by ring

private theorem one_sub_vecMulVec_mul_vecMulVec {v w ρ κ : Fin n → K} :
    (1 - Matrix.vecMulVec v w) * Matrix.vecMulVec ρ κ =
      Matrix.vecMulVec (ρ - (∑ i, w i * ρ i) • v) κ := by
  rw [Matrix.sub_mul, Matrix.one_mul, vecMulVec_mul_vecMulVec]
  ext i j
  simp only [Matrix.sub_apply, Matrix.vecMulVec_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

private theorem vecMulVec_mul_one_sub_vecMulVec {a b v w : Fin n → K} :
    Matrix.vecMulVec a b * (1 - Matrix.vecMulVec v w) =
      Matrix.vecMulVec a (b - (∑ i, b i * v i) • w) := by
  rw [Matrix.mul_sub, Matrix.mul_one, vecMulVec_mul_vecMulVec]
  ext i j
  simp only [Matrix.sub_apply, Matrix.vecMulVec_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

private theorem vecMulVec_smul_vec (c : K) (v w : Fin n → K) :
    Matrix.vecMulVec v (c • w) = c • Matrix.vecMulVec v w := by
  ext i j
  simp only [Matrix.vecMulVec_apply, Pi.smul_apply, Matrix.smul_apply, smul_eq_mul]
  ring

private theorem one_sub_mul_one_sub (A B : Matrix (Fin n) (Fin n) K) :
    (1 - A) * (1 - B) = 1 - A - B + A * B := by
  rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub, Matrix.mul_one]
  abel

theorem one_sub_vecMulVec_mul_self {v w : Fin n → K} (hwv : ∑ i, w i * v i = 2) :
    (1 - Matrix.vecMulVec v w) * (1 - Matrix.vecMulVec v w) = 1 := by
  have hsq : Matrix.vecMulVec v w * Matrix.vecMulVec v w =
      (2 : K) • Matrix.vecMulVec v w := by
    rw [vecMulVec_mul_vecMulVec, hwv, vecMulVec_smul_vec]
  rw [one_sub_mul_one_sub, hsq, two_smul]
  abel

theorem one_sub_vecMulVec_conj {v w ρ κ : Fin n → K} (hwv : ∑ i, w i * v i = 2) :
    (1 - Matrix.vecMulVec v w) * (1 - Matrix.vecMulVec ρ κ) * (1 - Matrix.vecMulVec v w) =
      1 - Matrix.vecMulVec (ρ - (∑ i, w i * ρ i) • v) (κ - (∑ i, κ i * v i) • w) := by
  have hXB : (1 - Matrix.vecMulVec v w) * (1 - Matrix.vecMulVec ρ κ) =
      (1 - Matrix.vecMulVec v w) - (1 - Matrix.vecMulVec v w) * Matrix.vecMulVec ρ κ := by
    rw [Matrix.mul_sub, Matrix.mul_one]
  have h1 : (1 - Matrix.vecMulVec v w) * (1 - Matrix.vecMulVec ρ κ) *
        (1 - Matrix.vecMulVec v w) =
      1 - (1 - Matrix.vecMulVec v w) * Matrix.vecMulVec ρ κ *
        (1 - Matrix.vecMulVec v w) := by
    rw [hXB, Matrix.sub_mul, one_sub_vecMulVec_mul_self hwv]
  rw [h1, one_sub_vecMulVec_mul_vecMulVec, vecMulVec_mul_one_sub_vecMulVec]

end Matrices

section Words

variable {K : Type} [Field K]

theorem diagSignMat_zero_eq :
    (diagSignMat 0 : Matrix (Fin 4) (Fin 4) K) =
      1 - Matrix.vecMulVec ![1, 0, 0, 0] ![2, 0, 0, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [diagSignMat]
  ring

theorem pijMat_zero_one_eq :
    (pijMat 0 1 1 : Matrix (Fin 4) (Fin 4) K) =
      1 - Matrix.vecMulVec ![1, -1, 0, 0] ![1, -1, 0, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pijMat]

theorem pijMat_one_two_eq :
    (pijMat 1 2 1 : Matrix (Fin 4) (Fin 4) K) =
      1 - Matrix.vecMulVec ![0, 1, -1, 0] ![0, 1, -1, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pijMat]

theorem aba_mat_eq :
    (diagSignMat 0 * pijMat 0 1 1 * diagSignMat 0 : Matrix (Fin 4) (Fin 4) K) =
      1 - Matrix.vecMulVec ![1, 1, 0, 0] ![1, 1, 0, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [diagSignMat, pijMat, Matrix.mul_apply, Fin.sum_univ_four]

theorem bab_mat_eq :
    (pijMat 0 1 1 * diagSignMat 0 * pijMat 0 1 1 : Matrix (Fin 4) (Fin 4) K) =
      1 - Matrix.vecMulVec ![0, 1, 0, 0] ![0, 2, 0, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [diagSignMat, pijMat, Matrix.mul_apply, Fin.sum_univ_four]
  ring

theorem cbabc_mat_eq :
    (pijMat 1 2 1 * (pijMat 0 1 1 * diagSignMat 0 * pijMat 0 1 1) * pijMat 1 2 1 :
        Matrix (Fin 4) (Fin 4) K) =
      1 - Matrix.vecMulVec ![0, 0, 1, 0] ![0, 0, 2, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [diagSignMat, pijMat, Matrix.mul_apply, Fin.sum_univ_four]
  ring

theorem cabac_mat_eq :
    (pijMat 1 2 1 * (diagSignMat 0 * pijMat 0 1 1 * diagSignMat 0) * pijMat 1 2 1 :
        Matrix (Fin 4) (Fin 4) K) =
      1 - Matrix.vecMulVec ![1, 0, 1, 0] ![1, 0, 1, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [diagSignMat, pijMat, Matrix.mul_apply, Fin.sum_univ_four]

theorem bcb_mat_eq :
    (pijMat 0 1 1 * pijMat 1 2 1 * pijMat 0 1 1 : Matrix (Fin 4) (Fin 4) K) =
      1 - Matrix.vecMulVec ![1, 0, -1, 0] ![1, 0, -1, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pijMat, Matrix.mul_apply, Fin.sum_univ_four]

theorem halfOnesMat_eq :
    (halfOnesMat 4 : Matrix (Fin 4) (Fin 4) K) =
      1 - Matrix.vecMulVec (fun _ => 1) ((2 : K)⁻¹ • fun _ => 1) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [halfOnesMat, Matrix.vecMulVec_apply, Pi.smul_apply]

end Words

end CFSG.StandardType.ZS.FFourCoord

end
