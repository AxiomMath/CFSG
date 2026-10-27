module

public import CFSG.RankThree.GF2n.Smith81.Sec216LocalE3

public section

namespace CFSG.RankThree.GF2n.Smith81.S81C

open Matrix

variable {K : Type} [Field K] {n : ℕ}

private theorem s81c_rank_vecMulVec_eq_one {u w : Fin n → K} (hu : u ≠ 0) (hw : w ≠ 0) :
    (vecMulVec u w).rank = 1 := by
  apply le_antisymm (Matrix.rank_vecMulVec_le u w)
  obtain ⟨j, hj⟩ := Function.ne_iff.1 hw
  rw [Nat.one_le_iff_ne_zero]
  intro h0
  rw [Matrix.rank_eq_finrank_span_cols, Submodule.finrank_eq_zero] at h0
  have hcol : (vecMulVec u w).col j ∈ Submodule.span K (Set.range (vecMulVec u w).col) :=
    Submodule.subset_span ⟨j, rfl⟩
  rw [h0, Submodule.mem_bot] at hcol
  apply hu
  have h1 : w j • u = 0 := by
    rw [← hcol]
    ext i
    simp [Matrix.vecMulVec_apply, mul_comm]
  exact (smul_eq_zero.1 h1).resolve_left hj

theorem isTransvectionMat_of_vecMulVec {u φ : Fin n → K} (hu : u ≠ 0) (hφ : φ ≠ 0)
    (huφ : φ ⬝ᵥ u = 0) {k : GL (Fin n) K}
    (hk : (k : Matrix (Fin n) (Fin n) K) = 1 + vecMulVec u φ) : IsTransvectionMat k := by
  have hsub : (k : Matrix (Fin n) (Fin n) K) - 1 = vecMulVec u φ := by
    rw [hk, add_sub_cancel_left]
  refine ⟨?_, ?_⟩
  · rw [hsub, vecMulVec_mul_vecMulVec, huφ, zero_smul]
    simp
  · rw [hsub]
    exact s81c_rank_vecMulVec_eq_one hu hφ

end CFSG.RankThree.GF2n.Smith81.S81C
