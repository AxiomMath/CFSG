module

public import CFSG.RankThree.GF2n.Smith81.S81VBlock
public import CFSG.RankThree.GF2n.Smith81.S81VDefs

public section

namespace CFSG.RankThree.GF2n.Smith81.S81V

open CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary CFSG.RankThree.GF2n.Smith81.U6Cube Module Matrix

variable {F : Type} [Field F] {σ : F ≃+* F} {a b : Fin 3 → Fin 6 → F}

private theorem b2_fam_inl (j : Fin 3) : fam a b (Sum.inl j) = a j := rfl

private theorem b2_fam_inr (j : Fin 3) : fam a b (Sum.inr j) = b j := rfl

@[expose] def Herm (σ : F ≃+* F) : Submodule (Fσ σ) (Matrix (Fin 3) (Fin 3) F) where
  carrier := {H | cT σ H = H}
  add_mem' {H H'} hH hH' := by
    show cT σ (H + H') = H + H'
    rw [cT_add, (hH : cT σ H = H), (hH' : cT σ H' = H')]
  zero_mem' := by
    show cT σ (0 : Matrix (Fin 3) (Fin 3) F) = 0
    ext i j
    simp [cT_apply]
  smul_mem' c H hH := by
    show cT σ ((c : F) • H) = (c : F) • H
    rw [cT_smul, (hH : cT σ H = H), (c.2 : σ c = c)]

private theorem b2_cT_zero : cT σ (0 : Matrix (Fin 3) (Fin 3) F) = 0 := by
  ext i j
  simp [cT_apply]

theorem cT_nonsing_inv {ι : Type} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι F)
    (hA : A.det ≠ 0) : (cT σ A)⁻¹ = cT σ A⁻¹ := by
  apply Matrix.inv_eq_right_inv
  rw [← cT_mul, Matrix.nonsing_inv_mul A (isUnit_iff_ne_zero.mpr hA), cT_one]

theorem uU_unitary [CharP F 2] {H : Matrix (Fin 3) (Fin 3) F} (hH : cT σ H = H) :
    cT σ (Matrix.fromBlocks (1 : Matrix (Fin 3) (Fin 3) F) H 0 1) * Jm F *
      Matrix.fromBlocks (1 : Matrix (Fin 3) (Fin 3) F) H 0 1 = Jm F := by
  have hHH : H + H = 0 := by
    ext i j
    rw [Matrix.add_apply, Matrix.zero_apply]
    exact CharTwo.add_self_eq_zero _
  rw [cT_fromBlocks, cT_one, b2_cT_zero, hH]
  unfold Jm
  simp only [Matrix.fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, Matrix.one_mul,
    Matrix.mul_one, zero_add, add_zero]
  rw [hHH]

theorem uU_det {H : Matrix (Fin 3) (Fin 3) F} :
    (Matrix.fromBlocks (1 : Matrix (Fin 3) (Fin 3) F) H 0 1).det = 1 := by
  rw [Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, mul_one]

theorem levi_unitary (hσ : ∀ c, σ (σ c) = c) {A : Matrix (Fin 3) (Fin 3) F} (hA : A.det ≠ 0) :
    cT σ (Matrix.fromBlocks A 0 0 (cT σ A)⁻¹) * Jm F * Matrix.fromBlocks A 0 0 (cT σ A)⁻¹ = Jm F := by
  have hcA : (cT σ A).det ≠ 0 := by
    rw [det_cT]
    intro h
    exact hA (σ.injective (by rw [h, map_zero]))
  have hY : cT σ ((cT σ A)⁻¹) * A = 1 := by
    rw [cT_nonsing_inv A hA, cT_cT hσ, Matrix.nonsing_inv_mul A (isUnit_iff_ne_zero.mpr hA)]
  have hX : cT σ A * (cT σ A)⁻¹ = 1 := Matrix.mul_nonsing_inv (cT σ A) (isUnit_iff_ne_zero.mpr hcA)
  rw [cT_fromBlocks, b2_cT_zero]
  unfold Jm
  simp only [Matrix.fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, Matrix.one_mul,
    Matrix.mul_one, zero_add, add_zero]
  rw [hX, hY]

theorem levi_det {A : Matrix (Fin 3) (Fin 3) F} (hA : A.det ≠ 0) (hdet : σ A.det = A.det) :
    (Matrix.fromBlocks A 0 0 (cT σ A)⁻¹).det = 1 := by
  rw [Matrix.det_fromBlocks_zero₂₁, Matrix.det_nonsing_inv, det_cT, hdet]
  exact Ring.mul_inverse_cancel _ (isUnit_iff_ne_zero.mpr hA)

variable (hσ : ∀ c, σ (σ c) = c) (hf : Frame σ a b)

include hσ hf

noncomputable def uU [CharP F 2] (H : Matrix (Fin 3) (Fin 3) F) (hH : cT σ H = H) : SUid σ 6 :=
  ofGm hσ hf (Matrix.fromBlocks 1 H 0 1) (uU_unitary hH) uU_det

theorem gm_uU [CharP F 2] (H : Matrix (Fin 3) (Fin 3) F) (hH : cT σ H = H) :
    gm hσ hf (uU hσ hf H hH) = Matrix.fromBlocks 1 H 0 1 :=
  gm_ofGm hσ hf _ _ _

theorem uU_add [CharP F 2] (H H' : Matrix (Fin 3) (Fin 3) F) (hH : cT σ H = H) (hH' : cT σ H' = H')
    (hHH' : cT σ (H + H') = H + H') :
    uU hσ hf (H + H') hHH' = uU hσ hf H hH * uU hσ hf H' hH' := by
  apply gm_injective hσ hf
  rw [gm_mul, gm_uU, gm_uU, gm_uU, Matrix.fromBlocks_multiply]
  simp only [Matrix.mul_zero, Matrix.zero_mul, Matrix.one_mul, Matrix.mul_one, zero_add, add_zero]
  rw [add_comm H' H]

private theorem b2_gm_col (g : SUid σ 6) (j : Fin 3) (hg : g • a j = a j) (q : Fin 3 ⊕ Fin 3) :
    gm hσ hf g q (Sum.inl j) = (Pi.single (Sum.inl j) (1 : F) : Fin 3 ⊕ Fin 3 → F) q := by
  have hfb : g • fb hσ hf (Sum.inl j) = fb hσ hf (Sum.inl j) := by
    rw [fb_apply]
    exact hg
  have h1 := gm_repr hσ hf g (fb hσ hf (Sum.inl j))
  rw [hfb, Basis.repr_self, Finsupp.single_eq_pi_single, Matrix.mulVec_single_one] at h1
  exact (congrFun h1 q).symm

theorem mem_PtStab_iff [CharP F 2] (g : SUid σ 6) :
    g ∈ PtStab σ (Wa a) ↔ ∃ H, ∃ hH : cT σ H = H, g = uU hσ hf H hH := by
  constructor
  · intro hg
    have hfix : ∀ j, g • a j = a j := fun j =>
      hg (a j) (Submodule.subset_span (Set.mem_range_self j))
    have hcol : ∀ j q, gm hσ hf g q (Sum.inl j) = (Pi.single (Sum.inl j) (1 : F) : Fin 3 ⊕ Fin 3 → F) q :=
      fun j q => b2_gm_col hσ hf g j (hfix j) q
    obtain ⟨B, D, hblk⟩ : ∃ B D : Matrix (Fin 3) (Fin 3) F,
        gm hσ hf g = Matrix.fromBlocks 1 B 0 D := by
      refine ⟨Matrix.of fun i j => gm hσ hf g (Sum.inl i) (Sum.inr j),
        Matrix.of fun i j => gm hσ hf g (Sum.inr i) (Sum.inr j), ?_⟩
      ext (i | i) (j | j) <;> simp [hcol, Pi.single_apply, Matrix.one_apply, Matrix.of_apply]
    have hu := gm_unitary hσ hf g
    rw [hblk] at hu
    simp only [cT_fromBlocks, cT_one, b2_cT_zero, Jm, Matrix.fromBlocks_multiply,
      Matrix.fromBlocks_inj, Matrix.mul_zero, Matrix.zero_mul, Matrix.one_mul, Matrix.mul_one,
      zero_add, add_zero] at hu
    obtain ⟨-, hD, -, hBB⟩ := hu
    subst hD
    rw [cT_one, Matrix.one_mul, Matrix.mul_one] at hBB
    have hB : cT σ B = B := by
      ext i j
      have h := congrFun (congrFun hBB i) j
      simp only [Matrix.add_apply, Matrix.zero_apply] at h
      have hxx : B i j + B i j = 0 := CharTwo.add_self_eq_zero _
      linear_combination h - hxx
    refine ⟨B, hB, ?_⟩
    apply gm_injective hσ hf
    rw [gm_uU, hblk]
  · rintro ⟨H, hH, rfl⟩
    rw [mem_ptStab]
    have hfix : ∀ j, uU hσ hf H hH • a j = a j := by
      intro j
      have h := smul_fam hσ hf (uU hσ hf H hH) (Sum.inl j)
      rw [gm_uU, Fintype.sum_sum_type] at h
      simpa [b2_fam_inl, b2_fam_inr, Matrix.one_apply, ite_smul, Matrix.fromBlocks_apply₁₁,
        Matrix.fromBlocks_apply₂₁] using h
    have hker : Wa a ≤ LinearMap.ker (gLin (uU hσ hf H hH) - LinearMap.id) := by
      unfold Wa
      rw [Submodule.span_le]
      rintro _ ⟨j, rfl⟩
      simp only [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply,
        sub_eq_zero, gLin_apply]
      exact hfix j
    intro w hw
    have h := hker hw
    simp only [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero,
      gLin_apply] at h
    exact h

theorem uU_mem_PtStab [CharP F 2] (H : Matrix (Fin 3) (Fin 3) F) (hH : cT σ H = H) :
    uU hσ hf H hH ∈ PtStab σ (Wa a) :=
  (mem_PtStab_iff hσ hf _).2 ⟨H, hH, rfl⟩

theorem PtStab_le_Pstab [CharP F 2] : PtStab σ (Wa a) ≤ Pstab σ (Wa a) := by
  intro g hg
  show (Wa a).map (gLin g) = Wa a
  ext y
  rw [Submodule.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [gLin_apply, hg x hx]
    exact hx
  · intro hy
    exact ⟨y, hy, by rw [gLin_apply]; exact hg y hy⟩

noncomputable def levi (A : Matrix (Fin 3) (Fin 3) F) (hA : A.det ≠ 0) (hdet : σ A.det = A.det) :
    SUid σ 6 :=
  ofGm hσ hf (Matrix.fromBlocks A 0 0 (cT σ A)⁻¹) (levi_unitary hσ hA) (levi_det hA hdet)

theorem gm_levi (A : Matrix (Fin 3) (Fin 3) F) (hA : A.det ≠ 0) (hdet : σ A.det = A.det) :
    gm hσ hf (levi hσ hf A hA hdet) = Matrix.fromBlocks A 0 0 (cT σ A)⁻¹ :=
  gm_ofGm hσ hf _ _ _

theorem levi_mul (A B : Matrix (Fin 3) (Fin 3) F) (hA : A.det ≠ 0) (hB : B.det ≠ 0)
    (hdetA : σ A.det = A.det) (hdetB : σ B.det = B.det) (hAB : (A * B).det ≠ 0)
    (hdetAB : σ (A * B).det = (A * B).det) :
    levi hσ hf (A * B) hAB hdetAB = levi hσ hf A hA hdetA * levi hσ hf B hB hdetB := by
  apply gm_injective hσ hf
  rw [gm_mul]
  simp only [gm_levi]
  rw [cT_mul, Matrix.mul_inv_rev, Matrix.fromBlocks_multiply]
  simp

theorem levi_one : levi hσ hf (1 : Matrix (Fin 3) (Fin 3) F) (by simp) (by simp) = 1 := by
  have h1 : (1 : Matrix (Fin 3) (Fin 3) F)⁻¹ = 1 := Matrix.inv_eq_right_inv (Matrix.mul_one _)
  apply gm_injective hσ hf
  rw [gm_levi, gm_one, cT_one, h1, Matrix.fromBlocks_one]

theorem levi_mem_Pstab (A : Matrix (Fin 3) (Fin 3) F) (hA : A.det ≠ 0) (hdet : σ A.det = A.det) :
    levi hσ hf A hA hdet ∈ Pstab σ (Wa a) := by
  rw [mem_Pstab_iff hσ hf]
  intro i j
  simp [gm_levi]

end CFSG.RankThree.GF2n.Smith81.S81V
