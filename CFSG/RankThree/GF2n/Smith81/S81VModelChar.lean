module

public import CFSG.RankThree.GF2n.Smith81.S81VModelTorus

public section

namespace CFSG.RankThree.GF2n.Smith81.S81V

open CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary CFSG.RankThree.GF2n.Smith81.U6Cube Module Matrix

variable {F : Type} [Field F] [CharP F 2] {σ : F ≃+* F} {a b : Fin 3 → Fin 6 → F} {K : Type} [Field K]

theorem eq_one_of_sq_eq_one {L : Type} [Field L] [CharP L 2] {x : L} (h : x ^ 2 = 1) : x = 1 := by
  have h2 : (2 : L) = 0 := CharTwo.two_eq_zero
  have hmul : (x - 1) * (x - 1) = 0 := by linear_combination h + (1 - x) * h2
  exact sub_eq_zero.mp (mul_self_eq_zero.mp hmul)

theorem transvection_mul_self (i j : Fin 3) (hij : i ≠ j) (c : F) :
    Matrix.transvection i j c * Matrix.transvection i j c = 1 := by
  rw [Matrix.transvection_mul_transvection_same i j hij c c, CharTwo.add_self_eq_zero c,
    Matrix.transvection_zero]

private theorem transvection_det_ne (i j : Fin 3) (hij : i ≠ j) (c : F) :
    (Matrix.transvection i j c).det ≠ 0 := by
  rw [Matrix.det_transvection_of_ne i j hij c]
  exact one_ne_zero

private theorem transvection_det_fixed (i j : Fin 3) (hij : i ≠ j) (c : F) :
    σ (Matrix.transvection i j c).det = (Matrix.transvection i j c).det := by
  rw [Matrix.det_transvection_of_ne i j hij c, map_one]

private theorem dmat_det_ne {c : F} (hc : c ≠ 0) : (dmat c).det ≠ 0 := by
  rw [dmat_det]
  exact hc

private theorem dmat_det_fixed {c : F} (hc : σ c = c) : σ (dmat c).det = (dmat c).det := by
  rw [dmat_det]
  exact hc

private theorem split_mul_dmat (A : Matrix (Fin 3) (Fin 3) F) (hA : A.det ≠ 0) :
    A * dmat (A.det⁻¹) * dmat A.det = A := by
  rw [Matrix.mul_assoc, dmat_mul, inv_mul_cancel₀ hA, dmat_one, Matrix.mul_one]

private theorem det_mul_dmat_inv (A : Matrix (Fin 3) (Fin 3) F) (hA : A.det ≠ 0) :
    (A * dmat (A.det⁻¹)).det = 1 := by
  rw [Matrix.det_mul, dmat_det, mul_inv_cancel₀ hA]

private theorem sl_det_ne (M : Matrix.SpecialLinearGroup (Fin 3) F) :
    (M : Matrix (Fin 3) (Fin 3) F).det ≠ 0 := by
  have h : (M : Matrix (Fin 3) (Fin 3) F).det = 1 := M.2
  rw [h]
  exact one_ne_zero

private theorem sl_det_fixed (M : Matrix.SpecialLinearGroup (Fin 3) F) :
    σ (M : Matrix (Fin 3) (Fin 3) F).det = (M : Matrix (Fin 3) (Fin 3) F).det := by
  have h : (M : Matrix (Fin 3) (Fin 3) F).det = 1 := M.2
  rw [h, map_one]

private theorem chi_sq_one [CharP K 2] {G : Type} [Group G] (χ : G →* Kˣ) (x : G)
    (hx : x * x = 1) : χ x = 1 := by
  have hu : χ x * χ x = 1 := by rw [← map_mul, hx, map_one]
  have hu' : ((χ x : Kˣ) : K) * ((χ x : Kˣ) : K) = 1 := by rw [← Units.val_mul, hu, Units.val_one]
  have h2 : ((χ x : Kˣ) : K) ^ 2 = 1 := by rw [sq]; exact hu'
  exact Units.ext (eq_one_of_sq_eq_one h2)

variable (hσ : ∀ c, σ (σ c) = c) (hf : Frame σ a b) (e₀ : K ≃+* Fσ σ)

include hσ hf

@[expose] noncomputable def detK (g : ↥(Pstab σ (Wa a))) : Kˣ :=
  Units.mk0 (e₀.symm ⟨(blkA hσ hf g).det, blkA_det_fixed hσ hf g.2⟩)
    (by
      intro h
      apply blkA_det_ne hσ hf g.2
      have h2 := congrArg e₀ h
      rw [map_zero, RingEquiv.apply_symm_apply] at h2
      exact congrArg Subtype.val h2)

private theorem levi_eq5 (M N : Matrix (Fin 3) (Fin 3) F) (h : M = N) (hM : M.det ≠ 0)
    (hMσ : σ M.det = M.det) (hN : N.det ≠ 0) (hNσ : σ N.det = N.det) :
    levi hσ hf M hM hMσ = levi hσ hf N hN hNσ := by
  subst h
  rfl

private theorem chi_transvection [CharP K 2] (χ : ↥(Pstab σ (Wa a)) →* Kˣ) (i j : Fin 3) (hij : i ≠ j)
    (c : F) :
    χ (⟨levi hσ hf (Matrix.transvection i j c) (transvection_det_ne i j hij c)
        (transvection_det_fixed i j hij c),
      levi_mem_Pstab hσ hf _ (transvection_det_ne i j hij c) (transvection_det_fixed i j hij c)⟩ :
        ↥(Pstab σ (Wa a))) = 1 := by
  have hTT : Matrix.transvection i j c * Matrix.transvection i j c = 1 :=
    transvection_mul_self i j hij c
  have hT0 : (Matrix.transvection i j c).det ≠ 0 := transvection_det_ne i j hij c
  have hTσ : σ (Matrix.transvection i j c).det = (Matrix.transvection i j c).det :=
    transvection_det_fixed i j hij c
  have hTT0 : (Matrix.transvection i j c * Matrix.transvection i j c).det ≠ 0 := by
    rw [hTT, Matrix.det_one]
    exact one_ne_zero
  have hTTσ : σ (Matrix.transvection i j c * Matrix.transvection i j c).det =
      (Matrix.transvection i j c * Matrix.transvection i j c).det := by
    rw [hTT, Matrix.det_one, map_one]
  have hsq := levi_mul hσ hf _ _ hT0 hT0 hTσ hTσ hTT0 hTTσ
  have hone := (levi_eq5 hσ hf _ 1 hTT hTT0 hTTσ (by simp) (by simp)).trans (levi_one hσ hf)
  exact chi_sq_one χ (⟨levi hσ hf (Matrix.transvection i j c) hT0 hTσ,
      levi_mem_Pstab hσ hf _ hT0 hTσ⟩ : ↥(Pstab σ (Wa a))) (Subtype.ext (hsq.symm.trans hone))

private noncomputable def leviSL : Matrix.SpecialLinearGroup (Fin 3) F →* ↥(Pstab σ (Wa a)) where
  toFun M := ⟨levi hσ hf (M : Matrix (Fin 3) (Fin 3) F) (sl_det_ne M) (sl_det_fixed M),
    levi_mem_Pstab hσ hf _ (sl_det_ne M) (sl_det_fixed M)⟩
  map_one' := Subtype.ext (levi_one hσ hf)
  map_mul' M N := Subtype.ext (levi_mul hσ hf (M : Matrix (Fin 3) (Fin 3) F)
    (N : Matrix (Fin 3) (Fin 3) F) (sl_det_ne M) (sl_det_ne N) (sl_det_fixed M) (sl_det_fixed N)
    (sl_det_ne (M * N)) (sl_det_fixed (M * N)))

private theorem chi_levi_det_one [CharP K 2] (χ : ↥(Pstab σ (Wa a)) →* Kˣ) (B : Matrix (Fin 3) (Fin 3) F)
    (hB : B.det = 1) (hB0 : B.det ≠ 0) (hBσ : σ B.det = B.det) :
    χ (⟨levi hσ hf B hB0 hBσ, levi_mem_Pstab hσ hf B hB0 hBσ⟩ : ↥(Pstab σ (Wa a))) = 1 := by
  have hle : Subgroup.closure (Set.range (Matrix.TransvectionStruct.toSpecialLinearGroup :
      Matrix.TransvectionStruct (Fin 3) F → Matrix.SpecialLinearGroup (Fin 3) F)) ≤
      (χ.comp (leviSL hσ hf)).ker := by
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨t, rfl⟩
    rw [SetLike.mem_coe, MonoidHom.mem_ker, MonoidHom.comp_apply]
    exact chi_transvection hσ hf χ t.i t.j t.hij t.c
  rw [Matrix.SpecialLinearGroup.closure_range_toSpecialLinearGroup_eq_top_of_field] at hle
  have hmem : (⟨B, hB⟩ : Matrix.SpecialLinearGroup (Fin 3) F) ∈ (χ.comp (leviSL hσ hf)).ker :=
    hle (Subgroup.mem_top _)
  exact MonoidHom.mem_ker.mp hmem

private theorem chi_levi_eq_dmat [CharP K 2] (χ : ↥(Pstab σ (Wa a)) →* Kˣ) (A : Matrix (Fin 3) (Fin 3) F)
    (hA0 : A.det ≠ 0) (hAσ : σ A.det = A.det) :
    χ (⟨levi hσ hf A hA0 hAσ, levi_mem_Pstab hσ hf A hA0 hAσ⟩ : ↥(Pstab σ (Wa a))) =
      χ (⟨levi hσ hf (dmat A.det) (dmat_det_ne hA0) (dmat_det_fixed hAσ),
        levi_mem_Pstab hσ hf (dmat A.det) (dmat_det_ne hA0) (dmat_det_fixed hAσ)⟩ :
          ↥(Pstab σ (Wa a))) := by
  have hc0 : (dmat A.det).det ≠ 0 := dmat_det_ne hA0
  have hcσ : σ (dmat A.det).det = (dmat A.det).det := dmat_det_fixed hAσ
  have hB1 : (A * dmat (A.det⁻¹)).det = 1 := det_mul_dmat_inv A hA0
  have hB0 : (A * dmat (A.det⁻¹)).det ≠ 0 := by
    rw [hB1]
    exact one_ne_zero
  have hBσ : σ (A * dmat (A.det⁻¹)).det = (A * dmat (A.det⁻¹)).det := by
    rw [hB1, map_one]
  have hBC0 : (A * dmat (A.det⁻¹) * dmat A.det).det ≠ 0 := by
    rw [split_mul_dmat A hA0]
    exact hA0
  have hBCσ : σ (A * dmat (A.det⁻¹) * dmat A.det).det =
      (A * dmat (A.det⁻¹) * dmat A.det).det := by
    rw [split_mul_dmat A hA0]
    exact hAσ
  have hsplit := levi_mul hσ hf (A * dmat (A.det⁻¹)) (dmat A.det) hB0 hc0 hBσ hcσ hBC0 hBCσ
  have hAeq := levi_eq5 hσ hf A (A * dmat (A.det⁻¹) * dmat A.det) (split_mul_dmat A hA0).symm hA0 hAσ
    hBC0 hBCσ
  have key : (⟨levi hσ hf A hA0 hAσ, levi_mem_Pstab hσ hf A hA0 hAσ⟩ : ↥(Pstab σ (Wa a))) =
      (⟨levi hσ hf (A * dmat (A.det⁻¹)) hB0 hBσ, levi_mem_Pstab hσ hf _ hB0 hBσ⟩ :
          ↥(Pstab σ (Wa a))) *
        (⟨levi hσ hf (dmat A.det) hc0 hcσ, levi_mem_Pstab hσ hf _ hc0 hcσ⟩ :
          ↥(Pstab σ (Wa a))) :=
    Subtype.ext (hAeq.trans hsplit)
  rw [key, map_mul, chi_levi_det_one hσ hf χ _ hB1 hB0 hBσ, one_mul]

theorem levi_char [Fintype K] [CharP K 2] (χ : ↥(Pstab σ (Wa a)) →* Kˣ)
    (hχ : ∀ g : ↥(Pstab σ (Wa a)), (g : SUid σ 6) ∈ PtStab σ (Wa a) → χ g = 1)
    (g : ↥(Pstab σ (Wa a))) : χ g = χ (dKhom hσ hf e₀ (detK hσ hf e₀ g)) := by
  have hA0 : (blkA hσ hf (g : SUid σ 6)).det ≠ 0 := blkA_det_ne hσ hf g.2
  have hAσ : σ (blkA hσ hf (g : SUid σ 6)).det = (blkA hσ hf (g : SUid σ 6)).det :=
    blkA_det_fixed hσ hf g.2
  obtain ⟨H, hH⟩ := Pstab_decomp hσ hf e₀ (g : SUid σ 6) g.2
  have hHmem : uK hσ hf H ∈ Pstab σ (Wa a) := PtStab_le_Pstab hσ hf (uK_mem_PtStab hσ hf H)
  have hLmem : levi hσ hf (blkA hσ hf (g : SUid σ 6)) hA0 hAσ ∈ Pstab σ (Wa a) :=
    levi_mem_Pstab hσ hf _ hA0 hAσ
  have hfac : g = (⟨uK hσ hf H, hHmem⟩ : ↥(Pstab σ (Wa a))) *
      (⟨levi hσ hf (blkA hσ hf (g : SUid σ 6)) hA0 hAσ, hLmem⟩ : ↥(Pstab σ (Wa a))) :=
    Subtype.ext hH
  have step1 : χ g = χ (⟨levi hσ hf (blkA hσ hf (g : SUid σ 6)) hA0 hAσ, hLmem⟩ :
      ↥(Pstab σ (Wa a))) := by
    refine (congrArg χ hfac).trans ?_
    rw [map_mul, hχ ⟨uK hσ hf H, hHmem⟩ (uK_mem_PtStab hσ hf H), one_mul]
  have hcu : ((e₀ ((detK hσ hf e₀ g : Kˣ) : K) : Fσ σ) : F) = (blkA hσ hf (g : SUid σ 6)).det := by
    unfold detK
    rw [Units.val_mk0, RingEquiv.apply_symm_apply]
  have hdK : (⟨levi hσ hf (dmat (blkA hσ hf (g : SUid σ 6)).det) (dmat_det_ne hA0) (dmat_det_fixed hAσ),
      levi_mem_Pstab hσ hf (dmat (blkA hσ hf (g : SUid σ 6)).det) (dmat_det_ne hA0)
        (dmat_det_fixed hAσ)⟩ : ↥(Pstab σ (Wa a))) = dKhom hσ hf e₀ (detK hσ hf e₀ g) :=
    Subtype.ext (levi_eq5 hσ hf _ _ (congrArg dmat hcu.symm) _ _ _ _)
  calc χ g = χ (⟨levi hσ hf (blkA hσ hf (g : SUid σ 6)) hA0 hAσ, hLmem⟩ : ↥(Pstab σ (Wa a))) := step1
    _ = χ (⟨levi hσ hf (dmat (blkA hσ hf (g : SUid σ 6)).det) (dmat_det_ne hA0) (dmat_det_fixed hAσ),
        levi_mem_Pstab hσ hf (dmat (blkA hσ hf (g : SUid σ 6)).det) (dmat_det_ne hA0)
          (dmat_det_fixed hAσ)⟩ : ↥(Pstab σ (Wa a))) := chi_levi_eq_dmat hσ hf χ _ hA0 hAσ
    _ = χ (dKhom hσ hf e₀ (detK hσ hf e₀ g)) := congrArg χ hdK

end CFSG.RankThree.GF2n.Smith81.S81V
