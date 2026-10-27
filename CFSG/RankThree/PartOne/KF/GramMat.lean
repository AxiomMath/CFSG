module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.RankThree.PartOne.KF.R9Perm

public section

namespace CFSG.RankThree.PartOne.KFU

open CFSG.LieType.Universal.Unitary Matrix

variable {p : ℕ} {K : Type} [Field K] {n : ℕ}

theorem diagU_gram (σ : K ≃+* K) {d : Fin n → Kˣ}
    (h : ∀ i, σ (d i : K) * (d (Fin.rev i) : K) = 1) :
    conjTr σ ((diagU d : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * antidiag n *
      ((diagU d : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = antidiag n := by
  ext i j
  simp only [conjTr, diagU_val, Matrix.diagonal_map (map_zero σ), Matrix.diagonal_transpose,
    Matrix.diagonal_mul, Matrix.mul_diagonal, antidiag, Matrix.of_apply]
  by_cases hj : j = Fin.rev i
  · subst hj
    simp [h i]
  · simp [hj]

theorem antidiag_eq_permMatrix : (antidiag n : Matrix (Fin n) (Fin n) K) =
    (Fin.revPerm : Equiv.Perm (Fin n)).permMatrix K := by
  ext i j
  simp [antidiag, PEquiv.toMatrix_apply, eq_comm]

theorem permGL_gram (σ : K ≃+* K) (τ : Equiv.Perm (Fin n))
    (h : ∀ i, τ (Fin.rev i) = Fin.rev (τ i)) :
    conjTr σ ((permGL τ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * antidiag n *
      ((permGL τ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = antidiag n := by
  rw [coe_permGL, antidiag_eq_permMatrix, conjTr]
  have hm : ((τ⁻¹).permMatrix K).map σ = (τ⁻¹).permMatrix K := by
    ext i j
    simp only [Matrix.map_apply, PEquiv.toMatrix_apply]
    split_ifs <;> simp
  rw [hm, Matrix.transpose_permMatrix, inv_inv, ← Matrix.permMatrix_mul, ← Matrix.permMatrix_mul]
  congr 1
  refine Equiv.ext fun i => ?_
  show τ⁻¹ (Fin.rev (τ i)) = Fin.rev i
  rw [← h i, Equiv.Perm.inv_def, Equiv.symm_apply_apply]

end CFSG.RankThree.PartOne.KFU
