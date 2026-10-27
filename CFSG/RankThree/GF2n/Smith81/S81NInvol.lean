module

public import CFSG.RankThree.GF2n.Smith81.S81A5KerRho
public import CFSG.RankThree.GF2n.Smith81.S81NTk
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotPositionBNormalForm

public noncomputable section

namespace CFSG.RankThree.GF2n.Smith81.A5Cube

open Matrix CFSG.SeitzReduction.LinearPilot

variable {K : Type*} [Field K]


private theorem s81n_permMatrix_apply (σ : Equiv.Perm (Fin 6)) (i k : Fin 6) :
    σ.permMatrix K i k = if σ i = k then 1 else 0 := by
  simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply]

private theorem s81n_permMatrix_mul (σ : Equiv.Perm (Fin 6)) (M : Matrix (Fin 6) (Fin 6) K) :
    σ.permMatrix K * M = M.submatrix σ σ * σ.permMatrix K := by
  ext i j
  have hL : (σ.permMatrix K * M) i j = M (σ i) j := by
    simp [Matrix.mul_apply, s81n_permMatrix_apply, ite_mul]
  have hR : (M.submatrix σ σ * σ.permMatrix K) i j = M (σ i) j := by
    rw [Matrix.mul_apply, Finset.sum_eq_single (σ.symm j)]
    · simp [s81n_permMatrix_apply]
    · intro k _ hk
      have hkj : σ k ≠ j := fun h => hk (by rw [← h, Equiv.symm_apply_apply])
      simp [s81n_permMatrix_apply, hkj]
    · intro h
      exact absurd (Finset.mem_univ _) h
  rw [hL, hR]

private theorem s81n_submatrix_nilOf (σ : Equiv.Perm (Fin 6)) {k : ℕ} (u w su sw : Fin k → Fin 6)
    (hsu : ∀ a, σ (su a) = u a) (hsw : ∀ a, σ (sw a) = w a) :
    (nilOf K u w).submatrix σ σ = nilOf K su sw := by
  ext i j
  have hiff : (∃ a, u a = σ i ∧ w a = σ j) ↔ (∃ a, su a = i ∧ sw a = j) := by
    constructor
    · rintro ⟨a, ha1, ha2⟩
      exact ⟨a, σ.injective ((hsu a).trans ha1), σ.injective ((hsw a).trans ha2)⟩
    · rintro ⟨a, rfl, rfl⟩
      exact ⟨a, (hsu a).symm, (hsw a).symm⟩
  simp only [Matrix.submatrix_apply, nilOf_apply, hiff]

private theorem s81n_exists_perm {k : ℕ} (u w su sw : Fin k → Fin 6)
    (hu : Function.Injective u) (hw : Function.Injective w) (huw : ∀ a b, u a ≠ w b)
    (hsu : Function.Injective su) (hsw : Function.Injective sw) (hsuw : ∀ a b, su a ≠ sw b) :
    ∃ σ : Equiv.Perm (Fin 6), ∀ a, σ (su a) = u a ∧ σ (sw a) = w a := by
  classical
  let f : Fin k ⊕ Fin k → Fin 6 := Sum.elim u w
  let g : Fin k ⊕ Fin k → Fin 6 := Sum.elim su sw
  have hf : Function.Injective f := by
    rintro (a | a) (b | b) hab
    · exact congrArg Sum.inl (hu hab)
    · exact (huw a b hab).elim
    · exact (huw b a hab.symm).elim
    · exact congrArg Sum.inr (hw hab)
  have hg : Function.Injective g := by
    rintro (a | a) (b | b) hab
    · exact congrArg Sum.inl (hsu hab)
    · exact (hsuw a b hab).elim
    · exact (hsuw b a hab.symm).elim
    · exact congrArg Sum.inr (hsw hab)
  let e : Set.range g ≃ Set.range f :=
    (Equiv.ofInjective g hg).symm.trans (Equiv.ofInjective f hf)
  have key : ∀ x : Fin k ⊕ Fin k, e.extendSubtype (g x) = f x := by
    intro x
    rw [Equiv.extendSubtype_apply_of_mem e (g x) (Set.mem_range_self x)]
    simp [e, Equiv.ofInjective_symm_apply hg x]
  exact ⟨e.extendSubtype, fun a => ⟨key (Sum.inl a), key (Sum.inr a)⟩⟩

private theorem s81n_mul_eq_of_conj (g A : Matrix.SpecialLinearGroup (Fin 6) K)
    (N : Matrix (Fin 6) (Fin 6) K)
    (h : ((g * A * g⁻¹ : Matrix.SpecialLinearGroup (Fin 6) K) :
      Matrix (Fin 6) (Fin 6) K) = 1 + N) :
    (g : Matrix (Fin 6) (Fin 6) K) * (A : Matrix (Fin 6) (Fin 6) K) =
      (1 + N) * (g : Matrix (Fin 6) (Fin 6) K) := by
  have hinv : ((g⁻¹ : Matrix.SpecialLinearGroup (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) *
      (g : Matrix (Fin 6) (Fin 6) K) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]
  rw [← h]
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_assoc, hinv, Matrix.mul_one]

private theorem s81n_conj_std [CharP K 2] {k : ℕ} (u w su sw : Fin k → Fin 6)
    (hu : Function.Injective u) (hw : Function.Injective w) (huw : ∀ a b, u a ≠ w b)
    (hsu : Function.Injective su) (hsw : Function.Injective sw) (hsuw : ∀ a b, su a ≠ sw b)
    (t G X : GL (Fin 6) K) (hGdet : (G : Matrix (Fin 6) (Fin 6) K).det = 1)
    (hGt : (G : Matrix (Fin 6) (Fin 6) K) * (t : Matrix (Fin 6) (Fin 6) K) =
      (1 + nilOf K u w) * (G : Matrix (Fin 6) (Fin 6) K))
    (hX : (X : Matrix (Fin 6) (Fin 6) K) = 1 + nilOf K su sw) :
    ∃ g' : GL (Fin 6) K, (g' : Matrix (Fin 6) (Fin 6) K).det = 1 ∧ g' * t * g'⁻¹ = X := by
  obtain ⟨σ, hσ⟩ := s81n_exists_perm u w su sw hu hw huw hsu hsw hsuw
  have hPdet : (σ.permMatrix K).det = 1 := by
    rw [Matrix.det_permutation]
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h, CharTwo.neg_eq]
  have hPne : (σ.permMatrix K).det ≠ 0 := by
    rw [hPdet]
    exact one_ne_zero
  obtain ⟨P, hPval⟩ : ∃ P : GL (Fin 6) K,
      (P : Matrix (Fin 6) (Fin 6) K) = σ.permMatrix K :=
    ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero _ hPne, rfl⟩
  have hkey : σ.permMatrix K * (1 + nilOf K u w) = (1 + nilOf K su sw) * σ.permMatrix K := by
    rw [mul_add, mul_one, add_mul, one_mul, s81n_permMatrix_mul σ (nilOf K u w),
      s81n_submatrix_nilOf σ u w su sw (fun a => (hσ a).1) (fun a => (hσ a).2)]
  refine ⟨P * G, ?_, ?_⟩
  · rw [Units.val_mul, Matrix.det_mul, hPval, hPdet, hGdet, one_mul]
  · rw [mul_inv_eq_iff_eq_mul]
    apply Units.ext
    simp only [Units.val_mul]
    calc (P : Matrix (Fin 6) (Fin 6) K) * (G : Matrix (Fin 6) (Fin 6) K) *
          (t : Matrix (Fin 6) (Fin 6) K)
        = (P : Matrix (Fin 6) (Fin 6) K) *
          ((G : Matrix (Fin 6) (Fin 6) K) * (t : Matrix (Fin 6) (Fin 6) K)) := by
          rw [mul_assoc]
      _ = (P : Matrix (Fin 6) (Fin 6) K) *
          ((1 + nilOf K u w) * (G : Matrix (Fin 6) (Fin 6) K)) := by
          rw [hGt]
      _ = ((P : Matrix (Fin 6) (Fin 6) K) * (1 + nilOf K u w)) *
          (G : Matrix (Fin 6) (Fin 6) K) := by
          rw [mul_assoc]
      _ = ((1 + nilOf K su sw) * (P : Matrix (Fin 6) (Fin 6) K)) *
          (G : Matrix (Fin 6) (Fin 6) K) := by
          rw [hPval, hkey]
      _ = (1 + nilOf K su sw) *
          ((P : Matrix (Fin 6) (Fin 6) K) * (G : Matrix (Fin 6) (Fin 6) K)) := by
          rw [mul_assoc]
      _ = (X : Matrix (Fin 6) (Fin 6) K) *
          ((P : Matrix (Fin 6) (Fin 6) K) * (G : Matrix (Fin 6) (Fin 6) K)) := by
          rw [hX]

private theorem s81n_nilOf_one :
    nilOf K (![0] : Fin 1 → Fin 6) ![1] = Matrix.single 0 1 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [nilOf_apply, Matrix.single_apply]

private theorem s81n_nilOf_two :
    nilOf K (![0, 2] : Fin 2 → Fin 6) ![1, 3] = Matrix.single 0 1 1 + Matrix.single 2 3 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [nilOf_apply, Matrix.single_apply, Fin.exists_fin_succ]

private theorem s81n_nilOf_three :
    nilOf K (![0, 2, 4] : Fin 3 → Fin 6) ![1, 3, 5] =
      Matrix.single 0 1 1 + Matrix.single 2 3 1 + Matrix.single 4 5 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [nilOf_apply, Matrix.single_apply, Fin.exists_fin_succ]

private theorem s81n_tInv1_val :
    (tInv1 K : Matrix (Fin 6) (Fin 6) K) = 1 + Matrix.single 0 1 1 := by
  rw [tInv1, transvGL_val, Matrix.transvection]

private theorem s81n_tInv2_val :
    (tInv2 K : Matrix (Fin 6) (Fin 6) K) = 1 + (Matrix.single 0 1 1 + Matrix.single 2 3 1) := by
  rw [tInv2, Units.val_mul, s81n_tInv1_val, transvGL_val, Matrix.transvection, add_mul, one_mul,
    mul_add, mul_one, Matrix.single_mul_single_of_ne (h := (by decide : (1 : Fin 6) ≠ 2)),
    add_zero]
  abel

private theorem s81n_tInv3_val :
    (tInv3 K : Matrix (Fin 6) (Fin 6) K) =
      1 + (Matrix.single 0 1 1 + Matrix.single 2 3 1 + Matrix.single 4 5 1) := by
  rw [tInv3, Units.val_mul, s81n_tInv2_val, transvGL_val, Matrix.transvection, add_mul, one_mul,
    mul_add, mul_one, add_mul, Matrix.single_mul_single_of_ne (h := (by decide : (1 : Fin 6) ≠ 4)),
    Matrix.single_mul_single_of_ne (h := (by decide : (3 : Fin 6) ≠ 4)), add_zero, add_zero]
  abel

private theorem s81n_tInv1_nil :
    (tInv1 K : Matrix (Fin 6) (Fin 6) K) = 1 + nilOf K (![0] : Fin 1 → Fin 6) ![1] := by
  rw [s81n_tInv1_val, s81n_nilOf_one]

private theorem s81n_tInv2_nil :
    (tInv2 K : Matrix (Fin 6) (Fin 6) K) = 1 + nilOf K (![0, 2] : Fin 2 → Fin 6) ![1, 3] := by
  rw [s81n_tInv2_val, s81n_nilOf_two]

private theorem s81n_tInv3_nil :
    (tInv3 K : Matrix (Fin 6) (Fin 6) K) =
      1 + nilOf K (![0, 2, 4] : Fin 3 → Fin 6) ![1, 3, 5] := by
  rw [s81n_tInv3_val, s81n_nilOf_three]

theorem exists_conj_tInv [Finite K] [CharP K 2] {t : GL (Fin 6) K}
    (hdet : (t : Matrix (Fin 6) (Fin 6) K).det = 1) (h2 : rho K t * rho K t = 1)
    (h1 : rho K t ≠ 1) :
    ∃ t' g : GL (Fin 6) K, (t' : Matrix (Fin 6) (Fin 6) K).det = 1 ∧ rho K t' = rho K t ∧
      (g : Matrix (Fin 6) (Fin 6) K).det = 1 ∧
      (g * t' * g⁻¹ = tInv1 K ∨ g * t' * g⁻¹ = tInv2 K ∨ g * t' * g⁻¹ = tInv3 K) := by
  obtain ⟨l, hl3, htt⟩ := (rho_eq_one_iff (t * t)).mp (by rw [rho_mul]; exact h2)
  have htt' : (t : Matrix (Fin 6) (Fin 6) K) * (t : Matrix (Fin 6) (Fin 6) K) = l • 1 := by
    rw [← Units.val_mul]
    exact htt
  have hl0 : l ≠ 0 := by
    rintro rfl
    norm_num at hl3
  have hne : (l • (t : Matrix (Fin 6) (Fin 6) K)).det ≠ 0 := by
    rw [Matrix.det_smul, hdet, mul_one, Fintype.card_fin]
    exact pow_ne_zero _ hl0
  obtain ⟨t', ht'val⟩ : ∃ t' : GL (Fin 6) K,
      (t' : Matrix (Fin 6) (Fin 6) K) = l • (t : Matrix (Fin 6) (Fin 6) K) :=
    ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero _ hne, rfl⟩
  have ht'det : (t' : Matrix (Fin 6) (Fin 6) K).det = 1 := by
    rw [ht'val, Matrix.det_smul, hdet, mul_one, Fintype.card_fin,
      show l ^ 6 = (l ^ 3) ^ 2 by ring, hl3, one_pow]
  have ht'rho : rho K t' = rho K t := by
    rw [rho_smul l ht'val, hl3, one_smul]
  have hl3' : l * l * l = 1 := by linear_combination hl3
  have ht'sq : (t' : Matrix (Fin 6) (Fin 6) K) * (t' : Matrix (Fin 6) (Fin 6) K) = 1 := by
    rw [ht'val, Matrix.smul_mul, Matrix.mul_smul, htt', smul_smul, smul_smul, hl3', one_smul]
  obtain ⟨A, hAt⟩ : ∃ A : Matrix.SpecialLinearGroup (Fin 6) K,
      (A : Matrix (Fin 6) (Fin 6) K) = (t' : Matrix (Fin 6) (Fin 6) K) :=
    ⟨⟨t', ht'det⟩, rfl⟩
  have hAA : A * A = 1 := by
    have h : ((A * A : Matrix.SpecialLinearGroup (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) =
        ((1 : Matrix.SpecialLinearGroup (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) := by
      rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one, hAt]
      exact ht'sq
    exact Matrix.SpecialLinearGroup.ext _ _ fun i j => congrFun (congrFun h i) j
  obtain ⟨k, u, w, hu, hw, huw, g, hg⟩ := exists_conj_eq_one_add_nilOf hAA
  have hgne : (g : Matrix (Fin 6) (Fin 6) K).det ≠ 0 := by
    rw [Matrix.SpecialLinearGroup.det_coe]
    exact one_ne_zero
  obtain ⟨G, hGval⟩ : ∃ G : GL (Fin 6) K,
      (G : Matrix (Fin 6) (Fin 6) K) = (g : Matrix (Fin 6) (Fin 6) K) :=
    ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero _ hgne, rfl⟩
  have hGdet : (G : Matrix (Fin 6) (Fin 6) K).det = 1 := by
    rw [hGval, Matrix.SpecialLinearGroup.det_coe]
  have hGt : (G : Matrix (Fin 6) (Fin 6) K) * (t' : Matrix (Fin 6) (Fin 6) K) =
      (1 + nilOf K u w) * (G : Matrix (Fin 6) (Fin 6) K) := by
    rw [hGval, ← hAt]
    exact s81n_mul_eq_of_conj g A _ hg
  rcases Nat.eq_zero_or_pos k with hk0 | hk1
  ·
    exfalso
    subst hk0
    apply h1
    have hN : nilOf K u w = 0 := by
      ext i j
      simp [nilOf_apply]
    have hG1 : G * t' = G := by
      apply Units.ext
      rw [Units.val_mul, hGt, hN, add_zero, one_mul]
    have ht1 : t' = 1 := mul_left_cancel (a := G) (by rw [mul_one]; exact hG1)
    rw [← ht'rho, ht1]
    exact (rho_eq_one_iff 1).mpr ⟨1, one_pow 3, by simp⟩
  have hk3 : k ≤ 3 := by
    have hinj : Function.Injective (Sum.elim u w : Fin k ⊕ Fin k → Fin 6) := by
      rintro (a | a) (b | b) hab
      · exact congrArg Sum.inl (hu hab)
      · exact (huw a b hab).elim
      · exact (huw b a hab.symm).elim
      · exact congrArg Sum.inr (hw hab)
    have hc := Fintype.card_le_of_injective _ hinj
    simp only [Fintype.card_sum, Fintype.card_fin] at hc
    omega
  interval_cases k
  · obtain ⟨g', hg'det, hconj⟩ := s81n_conj_std u w (![0] : Fin 1 → Fin 6) ![1] hu hw huw
      (by decide) (by decide) (by decide) t' G (tInv1 K) hGdet hGt s81n_tInv1_nil
    exact ⟨t', g', ht'det, ht'rho, hg'det, Or.inl hconj⟩
  · obtain ⟨g', hg'det, hconj⟩ := s81n_conj_std u w (![0, 2] : Fin 2 → Fin 6) ![1, 3] hu hw huw
      (by decide) (by decide) (by decide) t' G (tInv2 K) hGdet hGt s81n_tInv2_nil
    exact ⟨t', g', ht'det, ht'rho, hg'det, Or.inr (Or.inl hconj)⟩
  · obtain ⟨g', hg'det, hconj⟩ :=
      s81n_conj_std u w (![0, 2, 4] : Fin 3 → Fin 6) ![1, 3, 5] hu hw huw
        (by decide) (by decide) (by decide) t' G (tInv3 K) hGdet hGt s81n_tInv3_nil
    exact ⟨t', g', ht'det, ht'rho, hg'det, Or.inr (Or.inr hconj)⟩

end CFSG.RankThree.GF2n.Smith81.A5Cube

end
