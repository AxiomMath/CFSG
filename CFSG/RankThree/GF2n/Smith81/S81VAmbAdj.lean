module

public import CFSG.RankThree.GF2n.Smith81.S81VAmbMap
public import CFSG.RankThree.GF2n.Smith81.S81VAmbLine
public import CFSG.RankThree.GF2n.Smith81.S81VAmbLevi
public import CFSG.RankThree.GF2n.Smith81.S81VModelSwap

public section

namespace CFSG.RankThree.GF2n.Smith81.S81V

open CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary CFSG.RankThree.GF2n.Smith81.U6Cube Module Matrix

variable {F : Type} [Field F] [CharP F 2] {σ : F ≃+* F} {a b : Fin 3 → Fin 6 → F}

private theorem gu1c_swapM_apply (p q : Fin 3 ⊕ Fin 3) :
    swapM F p q = if q = Equiv.swap (Sum.inl (0 : Fin 3)) (Sum.inr (0 : Fin 3)) p then 1 else 0 := by
  simp only [swapM, Equiv.Perm.permMatrix, PEquiv.toMatrix_toPEquiv_apply, Pi.single_apply]

private theorem gu1c_Wa_eq : Wa a = Submodule.span F {a 0, a 1, a 2} := by
  unfold Wa
  congr 1
  ext x
  constructor
  · rintro ⟨i, rfl⟩
    fin_cases i <;> simp
  · intro hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩

private theorem gu1c_cT_single (τ : F) (hτ : σ τ = τ) :
    cT σ (τ • Matrix.single (0 : Fin 3) (0 : Fin 3) (1 : F)) = τ • Matrix.single 0 0 1 := by
  ext i j
  by_cases h : i = 0 ∧ j = 0
  · obtain ⟨rfl, rfl⟩ := h
    simp [cT_apply, Matrix.single_apply, hτ]
  · have h1 : ¬ ((0 : Fin 3) = j ∧ (0 : Fin 3) = i) := fun h' => h ⟨h'.2.symm, h'.1.symm⟩
    have h2 : ¬ ((0 : Fin 3) = i ∧ (0 : Fin 3) = j) := fun h' => h ⟨h'.1.symm, h'.2.symm⟩
    simp [cT_apply, Matrix.single_apply, h1, h2]

private theorem gu1c_sU_a0 (hσ : ∀ c, σ (σ c) = c) (hf : Frame σ a b) :
    gLin (sU hσ hf) (a 0) = b 0 := by
  have h : gLin (sU hσ hf) (a 0) = ∑ q, gm hσ hf (sU hσ hf) q (Sum.inl 0) • fam a b q :=
    smul_fam hσ hf (sU hσ hf) (Sum.inl 0)
  rw [h, gm_sU, Fintype.sum_sum_type]
  simp [Fin.sum_univ_three, gu1c_swapM_apply, Equiv.swap_apply_def, fam]

private theorem gu1c_sU_a1 (hσ : ∀ c, σ (σ c) = c) (hf : Frame σ a b) :
    gLin (sU hσ hf) (a 1) = a 1 := by
  have h : gLin (sU hσ hf) (a 1) = ∑ q, gm hσ hf (sU hσ hf) q (Sum.inl 1) • fam a b q :=
    smul_fam hσ hf (sU hσ hf) (Sum.inl 1)
  rw [h, gm_sU, Fintype.sum_sum_type]
  simp [Fin.sum_univ_three, gu1c_swapM_apply, Equiv.swap_apply_def, fam]

private theorem gu1c_sU_a2 (hσ : ∀ c, σ (σ c) = c) (hf : Frame σ a b) :
    gLin (sU hσ hf) (a 2) = a 2 := by
  have h : gLin (sU hσ hf) (a 2) = ∑ q, gm hσ hf (sU hσ hf) q (Sum.inl 2) • fam a b q :=
    smul_fam hσ hf (sU hσ hf) (Sum.inl 2)
  rw [h, gm_sU, Fintype.sum_sum_type]
  simp [Fin.sum_univ_three, gu1c_swapM_apply, Equiv.swap_apply_def, fam]

private theorem gu1c_uU_b0 (hσ : ∀ c, σ (σ c) = c) (hf : Frame σ a b) (τ : F)
    (hH : cT σ (τ • Matrix.single (0 : Fin 3) (0 : Fin 3) (1 : F)) = τ • Matrix.single 0 0 1) :
    gLin (uU hσ hf (τ • Matrix.single 0 0 1) hH) (b 0) = b 0 + τ • a 0 := by
  have h : gLin (uU hσ hf (τ • Matrix.single 0 0 1) hH) (b 0) =
      ∑ q, gm hσ hf (uU hσ hf (τ • Matrix.single 0 0 1) hH) q (Sum.inr 0) • fam a b q :=
    smul_fam hσ hf (uU hσ hf (τ • Matrix.single 0 0 1) hH) (Sum.inr 0)
  rw [h, gm_uU, Fintype.sum_sum_type]
  simp [Fin.sum_univ_three, fam, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₂,
    Matrix.one_apply, Matrix.single_apply, Matrix.smul_apply]
  abel

private theorem gu1c_uU_map_W₁ [CharP F 2] (hσ : ∀ c, σ (σ c) = c) (hf : Frame σ a b)
    (H : Matrix (Fin 3) (Fin 3) F) (hH : cT σ H = H) (τ : F) (hτ : H = τ • Matrix.single 0 0 1) :
    (Submodule.span F {b 0, a 1, a 2}).map (gLin (uU hσ hf H hH)) =
      Submodule.span F {b 0 + τ • a 0, a 1, a 2} := by
  subst hτ
  have ha : ∀ j, gLin (uU hσ hf (τ • Matrix.single 0 0 1) hH) (a j) = a j := fun j =>
    uU_mem_PtStab hσ hf _ hH (a j) (Submodule.subset_span (Set.mem_range_self j))
  rw [Submodule.map_span, Set.image_insert_eq, Set.image_insert_eq, Set.image_singleton,
    gu1c_uU_b0 hσ hf τ hH, ha 1, ha 2]

theorem sU_map_Wa (hσ : ∀ c, σ (σ c) = c) (hf : Frame σ a b) :
    (Wa a).map (gLin (sU hσ hf)) = Submodule.span F {b 0, a 1, a 2} := by
  rw [gu1c_Wa_eq, Submodule.map_span, Set.image_insert_eq, Set.image_insert_eq, Set.image_singleton,
    gu1c_sU_a0 hσ hf, gu1c_sU_a1 hσ hf, gu1c_sU_a2 hσ hf]

theorem uK_map_W₁ {K : Type} [Field K] (e₀ : K ≃+* Fσ σ) (hσ : ∀ c, σ (σ c) = c) (hf : Frame σ a b) (t : K) :
    (Submodule.span F {b 0, a 1, a 2}).map (gLin (uK hσ hf (t • n1K σ e₀))) =
      Submodule.span F {b 0 + ((e₀ t : Fσ σ) : F) • a 0, a 1, a 2} := by
  have hK : uK hσ hf (t • n1K σ e₀) =
      uU hσ hf (t • n1K σ e₀).mat (HermK.cT_mat (t • n1K σ e₀)) :=
    gm_injective hσ hf (by rw [gm_uK, gm_uU])
  rw [hK]
  exact gu1c_uU_map_W₁ hσ hf (t • n1K σ e₀).mat (HermK.cT_mat (t • n1K σ e₀)) ((e₀ t : Fσ σ) : F)
    (by rw [HermK.mat_smul, n1K_mat])

theorem exists_P_s_of_adjacent (hσ : IsUnitaryInvolution σ) (hf : Frame σ a b)
    {y : Submodule F (Fin 6 → F)} (hy : IsPt σ y) (hy2 : finrank F ↥(Wa a ⊓ y) = 2) :
    ∃ p ∈ Pstab σ (Wa a), y = (Wa a).map (gLin (p * sU hσ.invol hf)) := by
  have hinv : ∀ c, σ (σ c) = c := hσ.invol
  obtain ⟨A, hA, hdet, hpA⟩ := exists_levi_H₀ hinv hf (inf_le_left : Wa a ⊓ y ≤ Wa a) hy2
  obtain ⟨p₁, hp₁def⟩ : ∃ p₁ : SUid σ 6, p₁ = levi hinv hf A hA hdet := ⟨_, rfl⟩
  rw [← hp₁def] at hpA
  have hp₁ : p₁ ∈ Pstab σ (Wa a) := by
    rw [hp₁def]
    exact levi_mem_Pstab hinv hf A hA hdet
  have hWinv : (Wa a).map (gLin p₁⁻¹) = Wa a := (inv_mem hp₁ : p₁⁻¹ ∈ Pstab σ (Wa a))
  have e1 : gLin (1 : SUid σ 6) = LinearMap.id := LinearMap.ext gLin_one
  obtain ⟨y', hy'⟩ : ∃ y' : Submodule F (Fin 6 → F), y' = y.map (gLin p₁⁻¹) := ⟨_, rfl⟩
  have hy'pt : IsPt σ y' := by
    rw [hy']
    exact isPt_map p₁⁻¹ hy
  have h1 : (Wa a ⊓ y).map (gLin p₁⁻¹) = Wa a ⊓ y' := by
    rw [map_gLin_inf, hWinv, hy']
  have h2 : (Wa a ⊓ y).map (gLin p₁⁻¹) = Submodule.span F {a 1, a 2} := by
    rw [← hpA, map_map_gLin, inv_mul_cancel, e1, Submodule.map_id]
  have hWy' : Wa a ⊓ y' = Submodule.span F {a 1, a 2} := h1.symm.trans h2
  have hfin' : finrank F ↥(Wa a ⊓ y') = 2 := by
    rw [← h1, finrank_map_gLin]
    exact hy2
  have hle : Submodule.span F {a 1, a 2} ≤ y' := by
    rw [← hWy']
    exact inf_le_right
  rcases line_through_H₀ hinv hf hy'pt hle with hW | ⟨τ, hτ, hyτ⟩
  ·
    exfalso
    have h3 : finrank F ↥y' = 3 := hy'pt.2
    rw [hW, inf_idem] at hfin'
    rw [hW] at h3
    omega
  ·
    have hH : cT σ (τ • Matrix.single (0 : Fin 3) (0 : Fin 3) (1 : F)) = τ • Matrix.single 0 0 1 :=
      gu1c_cT_single τ hτ
    have hu : uU hinv hf (τ • Matrix.single 0 0 1) hH ∈ Pstab σ (Wa a) :=
      PtStab_le_Pstab hinv hf (uU_mem_PtStab hinv hf (τ • Matrix.single 0 0 1) hH)
    have hum := gu1c_uU_map_W₁ hinv hf (τ • Matrix.single 0 0 1) hH τ rfl
    have hall : (Wa a).map (gLin (uU hinv hf (τ • Matrix.single 0 0 1) hH * sU hinv hf)) = y' := by
      rw [← map_map_gLin, sU_map_Wa hinv hf, hum, hyτ]
    have hback : y = y'.map (gLin p₁) := by
      rw [hy', map_map_gLin, mul_inv_cancel, e1, Submodule.map_id]
    refine ⟨p₁ * uU hinv hf (τ • Matrix.single 0 0 1) hH, mul_mem hp₁ hu, ?_⟩
    rw [mul_assoc, ← map_map_gLin, hall]
    exact hback

end CFSG.RankThree.GF2n.Smith81.S81V
