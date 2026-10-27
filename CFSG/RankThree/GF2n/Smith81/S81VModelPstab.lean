module

public import CFSG.RankThree.GF2n.Smith81.S81VModelAd

public section

namespace CFSG.RankThree.GF2n.Smith81.S81V

open CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary CFSG.RankThree.GF2n.Smith81.U6Cube Module Matrix

variable {F : Type} [Field F] [CharP F 2] {σ : F ≃+* F} {a b : Fin 3 → Fin 6 → F} {K : Type} [Field K]

variable (hσ : ∀ c, σ (σ c) = c) (hf : Frame σ a b)

private theorem inv_det_props (A : Matrix (Fin 3) (Fin 3) F) (hA : A.det ≠ 0)
    (hdet : σ A.det = A.det) : (A⁻¹).det ≠ 0 ∧ σ (A⁻¹).det = (A⁻¹).det := by
  have h1 : (A⁻¹).det * A.det = 1 := by
    rw [← Matrix.det_mul, Matrix.nonsing_inv_mul A (isUnit_iff_ne_zero.mpr hA), Matrix.det_one]
  have h2 : σ (A⁻¹).det * A.det = 1 := by
    have h := congrArg σ h1
    rwa [map_mul, map_one, hdet] at h
  refine ⟨fun h0 => ?_, ?_⟩
  · rw [h0, zero_mul] at h1
    exact zero_ne_one h1
  · apply mul_right_cancel₀ hA
    rw [h2, h1]

include hσ hf

noncomputable def blkA (g : SUid σ 6) : Matrix (Fin 3) (Fin 3) F := (gm hσ hf g).toBlocks₁₁

theorem blkA_one : blkA hσ hf (1 : SUid σ 6) = 1 := by
  unfold blkA
  rw [gm_one hσ hf, ← Matrix.fromBlocks_one, Matrix.toBlocks_fromBlocks₁₁]

theorem blkA_mul {g h : SUid σ 6} (hg : g ∈ Pstab σ (Wa a)) (hh : h ∈ Pstab σ (Wa a)) :
    blkA hσ hf (g * h) = blkA hσ hf g * blkA hσ hf h := by
  obtain ⟨A, B, D, hgm, -, -, -⟩ := Pstab_blocks hσ hf g hg
  obtain ⟨A', B', D', hhm, -, -, -⟩ := Pstab_blocks hσ hf h hh
  unfold blkA
  rw [gm_mul hσ hf, hgm, hhm, Matrix.fromBlocks_multiply]
  simp only [Matrix.toBlocks_fromBlocks₁₁, Matrix.mul_zero, add_zero]

theorem blkA_det_ne {g : SUid σ 6} (hg : g ∈ Pstab σ (Wa a)) : (blkA hσ hf g).det ≠ 0 := by
  obtain ⟨A, B, D, hgm, hAD, -, -⟩ := Pstab_blocks hσ hf g hg
  have hAeq : blkA hσ hf g = A := by
    unfold blkA
    rw [hgm, Matrix.toBlocks_fromBlocks₁₁]
  have hdet : σ A.det * D.det = 1 := by
    have h := congrArg Matrix.det hAD
    rwa [Matrix.det_mul, det_cT, Matrix.det_one] at h
  rw [hAeq]
  intro h0
  rw [h0, map_zero, zero_mul] at hdet
  exact zero_ne_one hdet

theorem blkA_det_fixed {g : SUid σ 6} (hg : g ∈ Pstab σ (Wa a)) :
    σ (blkA hσ hf g).det = (blkA hσ hf g).det := by
  obtain ⟨A, B, D, hgm, hAD, -, -⟩ := Pstab_blocks hσ hf g hg
  have hAeq : blkA hσ hf g = A := by
    unfold blkA
    rw [hgm, Matrix.toBlocks_fromBlocks₁₁]
  have h1 : A.det * D.det = 1 := by
    have h := gm_det hσ hf g
    rwa [hgm, Matrix.det_fromBlocks_zero₂₁] at h
  have h2 : σ A.det * D.det = 1 := by
    have h := congrArg Matrix.det hAD
    rwa [Matrix.det_mul, det_cT, Matrix.det_one] at h
  have hD : D.det ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at h1
    exact zero_ne_one h1
  rw [hAeq]
  apply mul_right_cancel₀ hD
  rw [h2, h1]

theorem blkA_levi (A : Matrix (Fin 3) (Fin 3) F) (hA : A.det ≠ 0) (hdet : σ A.det = A.det) :
    blkA hσ hf (levi hσ hf A hA hdet) = A := by
  unfold blkA
  rw [gm_levi hσ hf A hA hdet, Matrix.toBlocks_fromBlocks₁₁]

theorem blkA_uK (e₀ : K ≃+* Fσ σ) (H : HermK σ e₀) : blkA hσ hf (uK hσ hf H) = 1 := by
  unfold blkA
  rw [gm_uK hσ hf H, Matrix.toBlocks_fromBlocks₁₁]

noncomputable def adK (e₀ : K ≃+* Fσ σ) : ↥(Pstab σ (Wa a)) →* (HermK σ e₀ ≃ₗ[K] HermK σ e₀) where
  toFun g := adEquiv e₀ hσ (blkA hσ hf g) (blkA_det_ne hσ hf g.2)
  map_one' := by
    apply LinearEquiv.ext
    intro H
    apply HermK.ext
    change (adEquiv e₀ hσ (blkA hσ hf ((1 : ↥(Pstab σ (Wa a))) : SUid σ 6))
      (blkA_det_ne hσ hf (1 : ↥(Pstab σ (Wa a))).2) H).mat = H.mat
    rw [adEquiv_mat, Subgroup.coe_one, blkA_one hσ hf, Matrix.one_mul, cT_one, Matrix.mul_one]
  map_mul' g h := by
    apply LinearEquiv.ext
    intro H
    apply HermK.ext
    change (adEquiv e₀ hσ (blkA hσ hf ((g * h : ↥(Pstab σ (Wa a))) : SUid σ 6))
      (blkA_det_ne hσ hf (g * h : ↥(Pstab σ (Wa a))).2) H).mat =
      (adEquiv e₀ hσ (blkA hσ hf g) (blkA_det_ne hσ hf g.2)
        (adEquiv e₀ hσ (blkA hσ hf h) (blkA_det_ne hσ hf h.2) H)).mat
    rw [adEquiv_mat, adEquiv_mat, adEquiv_mat, Subgroup.coe_mul, blkA_mul hσ hf g.2 h.2, cT_mul]
    simp only [Matrix.mul_assoc]

theorem adK_mat (e₀ : K ≃+* Fσ σ) (g : ↥(Pstab σ (Wa a))) (H : HermK σ e₀) :
    (adK hσ hf e₀ g H).mat = blkA hσ hf g * H.mat * cT σ (blkA hσ hf g) := by
  rfl

theorem uK_adK (e₀ : K ≃+* Fσ σ) (g : ↥(Pstab σ (Wa a))) (H : HermK σ e₀) :
    uK hσ hf (adK hσ hf e₀ g H) = (g : SUid σ 6) * uK hσ hf H * (g : SUid σ 6)⁻¹ := by
  obtain ⟨A, B, D, hg, hAD, -, -⟩ := Pstab_blocks hσ hf (g : SUid σ 6) g.2
  have hAeq : blkA hσ hf (g : SUid σ 6) = A := by
    unfold blkA
    rw [hg, Matrix.toBlocks_fromBlocks₁₁]
  have hcomm : (g : SUid σ 6) * uK hσ hf H = uK hσ hf (adK hσ hf e₀ g H) * (g : SUid σ 6) := by
    refine gm_injective hσ hf ?_
    rw [gm_mul hσ hf, gm_mul hσ hf, gm_uK hσ hf, gm_uK hσ hf, adK_mat, hAeq, hg,
      Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
    have e1 : A * H.mat * cT σ A * D = A * H.mat := by
      rw [Matrix.mul_assoc (A * H.mat) (cT σ A) D, hAD, Matrix.mul_one]
    refine Matrix.fromBlocks_inj.mpr ⟨?_, ?_, ?_, ?_⟩
    · simp
    · rw [e1, Matrix.mul_one, Matrix.one_mul, add_comm]
    · simp
    · simp
  rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]

private theorem levi_congr (M N : Matrix (Fin 3) (Fin 3) F) (h : M = N) (hM : M.det ≠ 0)
    (hMσ : σ M.det = M.det) (hN : N.det ≠ 0) (hNσ : σ N.det = N.det) :
    levi hσ hf M hM hMσ = levi hσ hf N hN hNσ := by
  subst h
  rfl

private theorem Pstab_decomp_core (e₀ : K ≃+* Fσ σ) (g : SUid σ 6) (A B D : Matrix (Fin 3) (Fin 3) F)
    (hgm : gm hσ hf g = Matrix.fromBlocks A B 0 D) (hAD : cT σ A * D = 1)
    (hA : A.det ≠ 0) (hdet : σ A.det = A.det) :
    ∃ H : HermK σ e₀, g = uK hσ hf H * levi hσ hf A hA hdet := by
  have hDE : D * cT σ A = 1 := mul_eq_one_comm.mp hAD
  obtain ⟨hAi, hdeti⟩ := inv_det_props A hA hdet
  have hEA : (cT σ (A⁻¹))⁻¹ = cT σ A := by
    apply Matrix.inv_eq_left_inv
    rw [← cT_mul, Matrix.nonsing_inv_mul A (isUnit_iff_ne_zero.mpr hA), cT_one]
  have hu_gm : gm hσ hf (g * levi hσ hf (A⁻¹) hAi hdeti) =
      Matrix.fromBlocks 1 (B * cT σ A) 0 1 := by
    rw [gm_mul hσ hf, gm_levi hσ hf (A⁻¹) hAi hdeti, hEA, hgm, Matrix.fromBlocks_multiply]
    refine Matrix.fromBlocks_inj.mpr ⟨?_, ?_, ?_, ?_⟩
    · rw [Matrix.mul_zero, add_zero, Matrix.mul_nonsing_inv A (isUnit_iff_ne_zero.mpr hA)]
    · rw [Matrix.mul_zero, zero_add]
    · rw [Matrix.zero_mul, Matrix.mul_zero, add_zero]
    · rw [Matrix.zero_mul, zero_add, hDE]
  have hfixa : ∀ j : Fin 3, (g * levi hσ hf (A⁻¹) hAi hdeti) • a j = a j := by
    intro j
    show (g * levi hσ hf (A⁻¹) hAi hdeti) • fam a b (Sum.inl j) = fam a b (Sum.inl j)
    rw [smul_fam hσ hf, hu_gm, Fintype.sum_sum_type]
    simp [fam, Matrix.one_apply, ite_smul]
  have hfixW : ∀ w ∈ Wa a, (g * levi hσ hf (A⁻¹) hAi hdeti) • w = w := by
    intro w hw
    have hle : Wa a ≤ LinearMap.eqLocus (gLin (g * levi hσ hf (A⁻¹) hAi hdeti)) LinearMap.id := by
      unfold Wa
      rw [Submodule.span_le]
      rintro _ ⟨j, rfl⟩
      rw [SetLike.mem_coe, LinearMap.mem_eqLocus, gLin_apply, LinearMap.id_apply]
      exact hfixa j
    have h := LinearMap.mem_eqLocus.mp (hle hw)
    rw [gLin_apply, LinearMap.id_apply] at h
    exact h
  have hu : g * levi hσ hf (A⁻¹) hAi hdeti ∈ PtStab σ (Wa a) :=
    (mem_ptStab (σ := σ)).mpr hfixW
  obtain ⟨H, hH⟩ := exists_uK_of_mem_PtStab (e₀ := e₀) hσ hf hu
  have hLL : levi hσ hf (A⁻¹) hAi hdeti * levi hσ hf A hA hdet = 1 := by
    have hAA : (A⁻¹) * A = 1 := Matrix.nonsing_inv_mul A (isUnit_iff_ne_zero.mpr hA)
    have hAB : ((A⁻¹) * A).det ≠ 0 := by
      rw [hAA, Matrix.det_one]
      exact one_ne_zero
    have hdAB : σ ((A⁻¹) * A).det = ((A⁻¹) * A).det := by
      rw [hAA, Matrix.det_one, map_one]
    rw [← levi_mul hσ hf (A⁻¹) A hAi hA hdeti hdet hAB hdAB,
      levi_congr hσ hf ((A⁻¹) * A) 1 hAA hAB hdAB (by simp) (by simp), levi_one hσ hf]
  refine ⟨H, ?_⟩
  rw [← hH, mul_assoc, hLL, mul_one]

theorem Pstab_decomp (e₀ : K ≃+* Fσ σ) (g : SUid σ 6) (hg : g ∈ Pstab σ (Wa a)) :
    ∃ H : HermK σ e₀, g = uK hσ hf H *
      levi hσ hf (blkA hσ hf g) (blkA_det_ne hσ hf hg) (blkA_det_fixed hσ hf hg) := by
  obtain ⟨A, B, D, hgm, hAD, -, -⟩ := Pstab_blocks hσ hf g hg
  have hAeq : blkA hσ hf g = A := by
    unfold blkA
    rw [hgm, Matrix.toBlocks_fromBlocks₁₁]
  exact Pstab_decomp_core hσ hf e₀ g (blkA hσ hf g) B D (by rw [hAeq]; exact hgm)
    (by rw [hAeq]; exact hAD) (blkA_det_ne hσ hf hg) (blkA_det_fixed hσ hf hg)

end CFSG.RankThree.GF2n.Smith81.S81V
