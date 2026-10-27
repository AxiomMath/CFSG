module

public import CFSG.RankThree.GF2n.Stroth80.Sec12NatDualSL

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG.Open CFSG.Open.StatedAPI Matrix

variable {F : Type} [Field F] {n : ℕ}

theorem vecMulVec_mulVec_eq_smul_dotProduct (c γ x : Fin n → F) :
    Matrix.vecMulVec c γ *ᵥ x = (γ ⬝ᵥ x) • c := by
  ext i
  simp only [Matrix.mulVec, dotProduct, Matrix.vecMulVec_apply, Pi.smul_apply, smul_eq_mul,
    Finset.sum_mul]
  exact Finset.sum_congr rfl fun j _ => by ring

theorem vecMulVec_mul_self_eq_zero (c γ : Fin n → F) (hγc : γ ⬝ᵥ c = 0) :
    Matrix.vecMulVec c γ * Matrix.vecMulVec c γ = 0 := by
  rw [Matrix.vecMulVec_mul_vecMulVec, hγc, zero_smul, Matrix.vecMulVec_zero]

theorem one_add_vecMulVec_mul_one_sub (c γ : Fin n → F) (hγc : γ ⬝ᵥ c = 0) :
    (1 + Matrix.vecMulVec c γ) * (1 - Matrix.vecMulVec c γ) = 1 := by
  have e : (1 + Matrix.vecMulVec c γ) * (1 - Matrix.vecMulVec c γ) =
      1 - Matrix.vecMulVec c γ * Matrix.vecMulVec c γ := by
    noncomm_ring
  rw [e, vecMulVec_mul_self_eq_zero c γ hγc, sub_zero]

theorem one_sub_vecMulVec_mul_one_add (c γ : Fin n → F) (hγc : γ ⬝ᵥ c = 0) :
    (1 - Matrix.vecMulVec c γ) * (1 + Matrix.vecMulVec c γ) = 1 := by
  have e : (1 - Matrix.vecMulVec c γ) * (1 + Matrix.vecMulVec c γ) =
      1 - Matrix.vecMulVec c γ * Matrix.vecMulVec c γ := by
    noncomm_ring
  rw [e, vecMulVec_mul_self_eq_zero c γ hγc, sub_zero]

theorem exists_gl_transv (c γ : Fin n → F) (hγc : γ ⬝ᵥ c = 0) :
    ∃ τ : GL (Fin n) F, (τ : Matrix (Fin n) (Fin n) F) = 1 + Matrix.vecMulVec c γ ∧
      ((τ⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = 1 - Matrix.vecMulVec c γ ∧
      τ ∈ StatedSL n F := by
  have hdet : (1 + Matrix.vecMulVec c γ : Matrix (Fin n) (Fin n) F).det = 1 := by
    rw [Matrix.vecMulVec_eq Unit c γ, Matrix.det_one_add_replicateCol_mul_replicateRow, hγc,
      add_zero]
  refine ⟨Units.mk _ _ (one_add_vecMulVec_mul_one_sub c γ hγc)
    (one_sub_vecMulVec_mul_one_add c γ hγc), rfl, rfl, ?_⟩
  exact mem_statedSL_of_det hdet

theorem transvGL_mulVec (A : GL (Fin n) F) (c γ : Fin n → F)
    (hA : (A : Matrix (Fin n) (Fin n) F) = 1 + Matrix.vecMulVec c γ) (x : Fin n → F) :
    (A : Matrix (Fin n) (Fin n) F) *ᵥ x = x + (γ ⬝ᵥ x) • c := by
  rw [hA, Matrix.add_mulVec, Matrix.one_mulVec, vecMulVec_mulVec_eq_smul_dotProduct]

theorem transvGL_tinv_mulVec (A : GL (Fin n) F) (c γ : Fin n → F)
    (hγc : γ ⬝ᵥ c = 0)
    (hA : (A : Matrix (Fin n) (Fin n) F) = 1 + Matrix.vecMulVec c γ) (y : Fin n → F) :
    ((tinvGL A : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *ᵥ y =
      y - (c ⬝ᵥ y) • γ := by
  have hmul : (A : Matrix (Fin n) (Fin n) F) * (1 - Matrix.vecMulVec c γ) = 1 := by
    rw [hA]
    exact one_add_vecMulVec_mul_one_sub c γ hγc
  have hinv : ((A⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
      1 - Matrix.vecMulVec c γ :=
    Units.inv_eq_of_mul_eq_one_right hmul
  rw [coe_tinvGL, hinv, Matrix.transpose_sub, Matrix.transpose_one,
    Matrix.transpose_vecMulVec, Matrix.sub_mulVec, Matrix.one_mulVec,
    vecMulVec_mulVec_eq_smul_dotProduct]

theorem exists_dotProduct_eq_of_ne_zero (γ : Fin n → F) (hγ : γ ≠ 0) (r : F) :
    ∃ x : Fin n → F, γ ⬝ᵥ x = r := by
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hγ
  rw [Pi.zero_apply] at hi
  refine ⟨Pi.single i ((γ i)⁻¹ * r), ?_⟩
  rw [dotProduct_single, mul_inv_cancel_left₀ hi]

end CFSG.RankThree.GF2n.Stroth80
