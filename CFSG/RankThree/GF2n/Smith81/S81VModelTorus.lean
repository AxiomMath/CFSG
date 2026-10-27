module

public import CFSG.RankThree.GF2n.Smith81.S81VModelPstab

public section

namespace CFSG.RankThree.GF2n.Smith81.S81V

open CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary CFSG.RankThree.GF2n.Smith81.U6Cube Module Matrix

variable {F : Type} [Field F] [CharP F 2] {σ : F ≃+* F} {a b : Fin 3 → Fin 6 → F} {K : Type} [Field K]

@[expose] def dmat (c : F) : Matrix (Fin 3) (Fin 3) F := Matrix.diagonal ![c, 1, 1]

theorem dmat_det (c : F) : (dmat c).det = c := by
  simp [dmat, Matrix.det_diagonal, Fin.prod_univ_three]

theorem dmat_mul (c c' : F) : dmat c * dmat c' = dmat (c * c') := by
  unfold dmat
  rw [Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  fin_cases i <;> simp

theorem dmat_one : dmat (1 : F) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [dmat, Matrix.diagonal_apply, Matrix.one_apply]

theorem dmat_conj_single (c : F) :
    dmat c * Matrix.single 0 0 (1 : F) * cT σ (dmat c) = (c * σ c) • Matrix.single 0 0 (1 : F) := by
  have hc : cT σ (dmat c) = dmat (σ c) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [cT_apply, dmat, Matrix.diagonal_apply]
  rw [hc]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, dmat, Matrix.diagonal_apply, Matrix.single_apply]

variable (hσ : ∀ c, σ (σ c) = c) (hf : Frame σ a b) (e₀ : K ≃+* Fσ σ)

include hσ hf

omit hσ hf in
theorem e₀_unit_ne_zero (c : Kˣ) : ((e₀ (c : K) : Fσ σ) : F) ≠ 0 := by
  intro h
  apply c.ne_zero
  apply e₀.injective
  apply Subtype.ext
  simpa using h

@[expose] noncomputable def dK (c : Kˣ) : SUid σ 6 :=
  levi hσ hf (dmat ((e₀ (c : K) : Fσ σ) : F)) (by rw [dmat_det]; exact e₀_unit_ne_zero e₀ c)
    (by rw [dmat_det]; exact (e₀ (c : K)).2)

theorem gm_dK (c : Kˣ) :
    gm hσ hf (dK hσ hf e₀ c) = Matrix.fromBlocks (dmat ((e₀ (c : K) : Fσ σ) : F)) 0 0 (cT σ (dmat ((e₀ (c : K) : Fσ σ) : F)))⁻¹ := by
  unfold dK
  exact gm_levi hσ hf _ _ _

theorem dK_mem_Pstab (c : Kˣ) : dK hσ hf e₀ c ∈ Pstab σ (Wa a) := by
  unfold dK
  exact levi_mem_Pstab hσ hf _ _ _

theorem dK_mul (c c' : Kˣ) : dK hσ hf e₀ (c * c') = dK hσ hf e₀ c * dK hσ hf e₀ c' := by
  apply gm_injective hσ hf
  rw [gm_mul, gm_dK, gm_dK, gm_dK]
  have hm : ((e₀ ((c * c' : Kˣ) : K) : Fσ σ) : F) =
      ((e₀ (c : K) : Fσ σ) : F) * ((e₀ (c' : K) : Fσ σ) : F) := by
    simp
  rw [hm, ← dmat_mul, Matrix.fromBlocks_multiply, cT_mul, Matrix.mul_inv_rev]
  simp

theorem dK_one : dK hσ hf e₀ (1 : Kˣ) = 1 := by
  apply gm_injective hσ hf
  rw [gm_dK, gm_one]
  have h1 : ((e₀ ((1 : Kˣ) : K) : Fσ σ) : F) = 1 := by simp
  have h2 : (1 : Matrix (Fin 3) (Fin 3) F)⁻¹ = 1 := Matrix.inv_eq_right_inv (Matrix.mul_one _)
  rw [h1, dmat_one, cT_one, h2, Matrix.fromBlocks_one]

@[expose] noncomputable def dKhom : Kˣ →* ↥(Pstab σ (Wa a)) where
  toFun c := ⟨dK hσ hf e₀ c, dK_mem_Pstab hσ hf e₀ c⟩
  map_one' := Subtype.ext (dK_one hσ hf e₀)
  map_mul' c c' := Subtype.ext (dK_mul hσ hf e₀ c c')

theorem dKhom_coe (c : Kˣ) : ((dKhom hσ hf e₀ c : ↥(Pstab σ (Wa a))) : SUid σ 6) = dK hσ hf e₀ c := rfl

theorem blkA_dK (c : Kˣ) : blkA hσ hf (dK hσ hf e₀ c) = dmat ((e₀ (c : K) : Fσ σ) : F) := by
  unfold dK
  exact blkA_levi hσ hf _ _ _

theorem adK_dKhom (c : Kˣ) :
    adK hσ hf e₀ (dKhom hσ hf e₀ c) (n1K σ e₀) = (c : K) ^ 2 • n1K σ e₀ := by
  have hfix : σ ((e₀ (c : K) : Fσ σ) : F) = ((e₀ (c : K) : Fσ σ) : F) := (e₀ (c : K)).2
  have h2 : ((e₀ ((c : K) ^ 2) : Fσ σ) : F) =
      ((e₀ (c : K) : Fσ σ) : F) * ((e₀ (c : K) : Fσ σ) : F) := by
    simp [map_pow, pow_two]
  apply HermK.ext
  rw [adK_mat, dKhom_coe, blkA_dK, HermK.mat_smul, n1K_mat, dmat_conj_single, hfix, h2]

end CFSG.RankThree.GF2n.Smith81.S81V
