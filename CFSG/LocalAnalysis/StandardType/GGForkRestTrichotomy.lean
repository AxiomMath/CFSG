module

public import CFSG.LocalAnalysis.StandardType.GGForkClassify

public section

namespace CFSG.StandardType

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem trc_coxeter_reindex_trans {ι κ μ : Type} (N : CoxeterMatrix ι) (e : ι ≃ κ)
    (f : κ ≃ μ) : (N.reindex e).reindex f = N.reindex (e.trans f) := by
  apply CoxeterMatrix.ext
  funext i j
  simp only [CoxeterMatrix.reindex_apply, Equiv.symm_trans_apply]

private theorem trc_coxeter_reindex_refl {ι : Type} (N : CoxeterMatrix ι) :
    N.reindex (Equiv.refl ι) = N := by
  apply CoxeterMatrix.ext
  funext i j
  simp only [CoxeterMatrix.reindex_apply, Equiv.refl_symm, Equiv.refl_apply]

private theorem trc_GGIsWeylMatrix_reindex {ι κ : Type} {M : CoxeterMatrix ι}
    (hM : GGIsWeylMatrix M) (f : ι ≃ κ) : GGIsWeylMatrix (M.reindex f) := by
  rcases hM with ⟨n, e, hn, h | ⟨hn2, h⟩ | ⟨hn4, h⟩⟩ | ⟨e, h⟩ | ⟨e, h⟩ | ⟨e, h⟩ | ⟨e, h⟩ |
    ⟨e, h⟩
  · exact Or.inl ⟨n, e.trans f, hn, Or.inl (by rw [h]; exact trc_coxeter_reindex_trans _ e f)⟩
  · exact Or.inl ⟨n, e.trans f, hn,
      Or.inr (Or.inl ⟨hn2, by rw [h]; exact trc_coxeter_reindex_trans _ e f⟩)⟩
  · exact Or.inl ⟨n, e.trans f, hn,
      Or.inr (Or.inr ⟨hn4, by rw [h]; exact trc_coxeter_reindex_trans _ e f⟩)⟩
  · exact Or.inr (Or.inl ⟨e.trans f, by rw [h]; exact trc_coxeter_reindex_trans _ e f⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨e.trans f, by rw [h]; exact trc_coxeter_reindex_trans _ e f⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl
      ⟨e.trans f, by rw [h]; exact trc_coxeter_reindex_trans _ e f⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨e.trans f, by rw [h]; exact trc_coxeter_reindex_trans _ e f⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      ⟨e.trans f, by rw [h]; exact trc_coxeter_reindex_trans _ e f⟩))))

private theorem trc_ggIsWeylMatrix_A (n : ℕ) (hn : 1 ≤ n) : GGIsWeylMatrix (CoxeterMatrix.A n) :=
  Or.inl ⟨n, Equiv.refl (Fin n), hn, Or.inl (trc_coxeter_reindex_refl _).symm⟩

private theorem trc_ggIsWeylMatrix_E6 : GGIsWeylMatrix CoxeterMatrix.E₆ :=
  Or.inr (Or.inl ⟨Equiv.refl (Fin 6), (trc_coxeter_reindex_refl _).symm⟩)

private theorem trc_ggIsWeylMatrix_E7 : GGIsWeylMatrix CoxeterMatrix.E₇ :=
  Or.inr (Or.inr (Or.inl ⟨Equiv.refl (Fin 7), (trc_coxeter_reindex_refl _).symm⟩))

private theorem trc_ggIsWeylMatrix_E8 : GGIsWeylMatrix CoxeterMatrix.E₈ :=
  Or.inr (Or.inr (Or.inr (Or.inl ⟨Equiv.refl (Fin 8), (trc_coxeter_reindex_refl _).symm⟩)))

private theorem trc_attachWeyl_of_reindex {m N : ℕ} {C₀ : Matrix (Fin m) (Fin m) ℤ} {k : Fin m}
    {C₁ : Matrix (Fin N) (Fin N) ℤ} (f : Fin N ≃ Option (Fin m))
    (h : ∀ i j, ggAttachCartan C₀ k (f i) (f j) = C₁ i j)
    {M₁ : CoxeterMatrix (Fin N)} (hW : GGIsWeylMatrix M₁) (hInt : GGIntCartan M₁ C₁) :
    GGAttachWeyl C₀ k := by
  have heq : ggAttachCartan C₀ k = Matrix.reindex f f C₁ := ggMatrix_eq_reindex f h
  refine ⟨M₁.reindex f, trc_GGIsWeylMatrix_reindex hW f, ?_⟩
  rw [heq]
  exact hInt.reindex f

private theorem trc_attachWeyl_of_iso {m N : ℕ} {C₀ : Matrix (Fin m) (Fin m) ℤ} {k : Fin m}
    {C₁ : Matrix (Fin N) (Fin N) ℤ} {M₁ : CoxeterMatrix (Fin N)}
    (φ : Fin N → Option (Fin m)) (hφ : Function.Bijective φ)
    (h : ∀ i j, ggAttachCartan C₀ k (φ i) (φ j) = C₁ i j)
    (hW : GGIsWeylMatrix M₁) (hInt : GGIntCartan M₁ C₁) : GGAttachWeyl C₀ k :=
  trc_attachWeyl_of_reindex (Equiv.ofBijective φ hφ) (by
    intro i j
    rw [Equiv.ofBijective_apply]
    exact h i j) hW hInt

private theorem trc_attachWeyl_of_equiv {Λ : Type} [Fintype Λ] [DecidableEq Λ] {Λ' : Type}
    [DecidableEq Λ']
    {C : Matrix Λ Λ ℤ} {C' : Matrix Λ' Λ' ℤ} (e : Λ' ≃ Λ)
    (hC : ∀ i j, C (e i) (e j) = C' i j) {k : Λ} {k' : Λ'}
    (hk : k = e k') (h : GGAttachWeyl C' k') : GGAttachWeyl C k := by
  obtain ⟨M', hW, hInt⟩ := h
  refine ⟨M'.reindex (Equiv.optionCongr e), trc_GGIsWeylMatrix_reindex hW _, ?_⟩
  have heq : ggAttachCartan C k = Matrix.reindex (Equiv.optionCongr e) (Equiv.optionCongr e)
      (ggAttachCartan C' k') := by
    refine ggMatrix_eq_reindex _ fun i j => ?_
    have h := congr_fun (congr_fun (ggAttachCartan_submatrix_optionCongr e hC hk) i) j
    simpa only [Matrix.submatrix_apply] using h
  rw [heq]
  exact hInt.reindex (Equiv.optionCongr e)

private theorem trc_attachNullPos_of_equiv {Λ : Type} {Λ' : Type} [Fintype Λ] [DecidableEq Λ]
    [Fintype Λ'] [DecidableEq Λ'] {C : Matrix Λ Λ ℤ} {C' : Matrix Λ' Λ' ℤ} (e : Λ' ≃ Λ)
    (hC : ∀ i j, C (e i) (e j) = C' i j) {k : Λ} {k' : Λ'}
    (hk : k = e k') (h : GGAttachNullPos C' k') : GGAttachNullPos C k := by
  have hk' : k' = e.symm k := by rw [hk, Equiv.symm_apply_apply]
  have hC' : ∀ i j, C' (e.symm i) (e.symm j) = C i j := by
    intro i j
    rw [← hC (e.symm i) (e.symm j), e.apply_symm_apply, e.apply_symm_apply]
  exact GGAttachNullPos.of_equiv e.symm hC' hk' h

private theorem trc_attachWeyl_A2_0 : GGAttachWeyl (CartanMatrix.A 2) 0 :=
  trc_attachWeyl_of_iso (C₁ := CartanMatrix.A 3) (M₁ := CoxeterMatrix.A 3)
    (fun i : Fin 3 => ![none, some (0 : Fin 2), some (1 : Fin 2)] i)
    (by decide +kernel)
    (by intro i j; fin_cases i <;> fin_cases j <;> decide +kernel)
    (trc_ggIsWeylMatrix_A 3 (by norm_num))
    (ggIntCartan_A 3)

private theorem trc_attachWeyl_A2_1 : GGAttachWeyl (CartanMatrix.A 2) 1 :=
  trc_attachWeyl_of_iso (C₁ := CartanMatrix.A 3) (M₁ := CoxeterMatrix.A 3)
    (fun i : Fin 3 => ![none, some (1 : Fin 2), some (0 : Fin 2)] i)
    (by decide +kernel)
    (by intro i j; fin_cases i <;> fin_cases j <;> decide +kernel)
    (trc_ggIsWeylMatrix_A 3 (by norm_num))
    (ggIntCartan_A 3)

private theorem trc_attachWeyl_D5_spin3 : GGAttachWeyl (CartanMatrix.D 5) ⟨3, by norm_num⟩ :=
  trc_attachWeyl_of_iso (C₁ := CartanMatrix.E 6) (M₁ := CoxeterMatrix.E₆)
    (fun i : Fin 6 => ![none, some (4 : Fin 5), some (3 : Fin 5), some (2 : Fin 5),
      some (1 : Fin 5), some (0 : Fin 5)] i)
    (by decide +kernel)
    (by intro i j; fin_cases i <;> fin_cases j <;> decide +kernel)
    trc_ggIsWeylMatrix_E6 ggIntCartan_E₆

private theorem trc_attachWeyl_D5_spin4 : GGAttachWeyl (CartanMatrix.D 5) ⟨4, by norm_num⟩ :=
  trc_attachWeyl_of_iso (C₁ := CartanMatrix.E 6) (M₁ := CoxeterMatrix.E₆)
    (fun i : Fin 6 => ![none, some (3 : Fin 5), some (4 : Fin 5), some (2 : Fin 5),
      some (1 : Fin 5), some (0 : Fin 5)] i)
    (by decide +kernel)
    (by intro i j; fin_cases i <;> fin_cases j <;> decide +kernel)
    trc_ggIsWeylMatrix_E6 ggIntCartan_E₆

private theorem trc_attachWeyl_D6_spin4 : GGAttachWeyl (CartanMatrix.D 6) ⟨4, by norm_num⟩ :=
  trc_attachWeyl_of_iso (C₁ := CartanMatrix.E 7) (M₁ := CoxeterMatrix.E₇)
    (fun i : Fin 7 => ![none, some (5 : Fin 6), some (4 : Fin 6), some (3 : Fin 6),
      some (2 : Fin 6), some (1 : Fin 6), some (0 : Fin 6)] i)
    (by decide +kernel)
    (by intro i j; fin_cases i <;> fin_cases j <;> decide +kernel)
    trc_ggIsWeylMatrix_E7 ggIntCartan_E₇

private theorem trc_attachWeyl_D6_spin5 : GGAttachWeyl (CartanMatrix.D 6) ⟨5, by norm_num⟩ :=
  trc_attachWeyl_of_iso (C₁ := CartanMatrix.E 7) (M₁ := CoxeterMatrix.E₇)
    (fun i : Fin 7 => ![none, some (4 : Fin 6), some (5 : Fin 6), some (3 : Fin 6),
      some (2 : Fin 6), some (1 : Fin 6), some (0 : Fin 6)] i)
    (by decide +kernel)
    (by intro i j; fin_cases i <;> fin_cases j <;> decide +kernel)
    trc_ggIsWeylMatrix_E7 ggIntCartan_E₇

private theorem trc_attachWeyl_D7_spin5 : GGAttachWeyl (CartanMatrix.D 7) ⟨5, by norm_num⟩ :=
  trc_attachWeyl_of_iso (C₁ := CartanMatrix.E 8) (M₁ := CoxeterMatrix.E₈)
    (fun i : Fin 8 => ![none, some (6 : Fin 7), some (5 : Fin 7), some (4 : Fin 7),
      some (3 : Fin 7), some (2 : Fin 7), some (1 : Fin 7), some (0 : Fin 7)] i)
    (by decide +kernel)
    (by intro i j; fin_cases i <;> fin_cases j <;> decide +kernel)
    trc_ggIsWeylMatrix_E8 ggIntCartan_E₈

private theorem trc_attachWeyl_D7_spin6 : GGAttachWeyl (CartanMatrix.D 7) ⟨6, by norm_num⟩ :=
  trc_attachWeyl_of_iso (C₁ := CartanMatrix.E 8) (M₁ := CoxeterMatrix.E₈)
    (fun i : Fin 8 => ![none, some (5 : Fin 7), some (6 : Fin 7), some (4 : Fin 7),
      some (3 : Fin 7), some (2 : Fin 7), some (1 : Fin 7), some (0 : Fin 7)] i)
    (by decide +kernel)
    (by intro i j; fin_cases i <;> fin_cases j <;> decide +kernel)
    trc_ggIsWeylMatrix_E8 ggIntCartan_E₈

private theorem trc_attachWeyl_E6_0 : GGAttachWeyl (CartanMatrix.E 6) 0 :=
  trc_attachWeyl_of_iso (C₁ := CartanMatrix.E 7) (M₁ := CoxeterMatrix.E₇)
    (fun i : Fin 7 => ![some (5 : Fin 6), some (1 : Fin 6), some (4 : Fin 6), some (3 : Fin 6),
      some (2 : Fin 6), some (0 : Fin 6), none] i)
    (by decide +kernel)
    (by intro i j; fin_cases i <;> fin_cases j <;> decide +kernel)
    trc_ggIsWeylMatrix_E7 ggIntCartan_E₇

private theorem trc_attachWeyl_E6_5 : GGAttachWeyl (CartanMatrix.E 6) 5 :=
  trc_attachWeyl_of_iso (C₁ := CartanMatrix.E 7) (M₁ := CoxeterMatrix.E₇)
    (fun i : Fin 7 => ![some (0 : Fin 6), some (1 : Fin 6), some (2 : Fin 6), some (3 : Fin 6),
      some (4 : Fin 6), some (5 : Fin 6), none] i)
    (by decide +kernel)
    (by intro i j; fin_cases i <;> fin_cases j <;> decide +kernel)
    trc_ggIsWeylMatrix_E7 ggIntCartan_E₇

private theorem trc_attachWeyl_E7_6 : GGAttachWeyl (CartanMatrix.E 7) 6 :=
  trc_attachWeyl_of_iso (C₁ := CartanMatrix.E 8) (M₁ := CoxeterMatrix.E₈)
    (fun i : Fin 8 => ![some (0 : Fin 7), some (1 : Fin 7), some (2 : Fin 7), some (3 : Fin 7),
      some (4 : Fin 7), some (5 : Fin 7), some (6 : Fin 7), none] i)
    (by decide +kernel)
    (by intro i j; fin_cases i <;> fin_cases j <;> decide +kernel)
    trc_ggIsWeylMatrix_E8 ggIntCartan_E₈

private theorem trc_nullPos_E6_1 : GGAttachNullPos (CartanMatrix.E 6) 1 :=
  ⟨fun | none => 1 | some i => ![1, 2, 2, 3, 2, 1] i, by decide +kernel, by decide +kernel⟩

private theorem trc_nullPos_E7_0 : GGAttachNullPos (CartanMatrix.E 7) 0 :=
  ⟨fun | none => 1 | some i => ![2, 2, 3, 4, 3, 2, 1] i, by decide +kernel, by decide +kernel⟩

private theorem trc_nullPos_E8_7 : GGAttachNullPos (CartanMatrix.E 8) 7 :=
  ⟨fun | none => 1 | some i => ![2, 3, 4, 6, 5, 4, 3, 2] i, by decide +kernel, by decide +kernel⟩

private theorem trc_nullPos_D8_7 : GGAttachNullPos (CartanMatrix.D 8) 7 :=
  ⟨fun | none => 2 | some i => ![1, 2, 3, 4, 5, 6, 3, 4] i, by decide +kernel, by decide +kernel⟩

private theorem trc_nullPos_F4_0 : GGAttachNullPos CartanMatrix.F₄ 0 :=
  ⟨fun | none => 1 | some i => ![2, 3, 4, 2] i, by decide +kernel, by decide +kernel⟩

private theorem trc_nullPos_F4_3 : GGAttachNullPos CartanMatrix.F₄ 3 :=
  ⟨fun | none => 1 | some i => ![1, 2, 3, 2] i, by decide +kernel, by decide +kernel⟩

private theorem trc_nullPos_F4T_0 : GGAttachNullPos (Matrix.transpose CartanMatrix.F₄) 0 :=
  ⟨fun | none => 1 | some i => ![2, 3, 2, 1] i, by decide +kernel, by decide +kernel⟩

private theorem trc_nullPos_F4T_3 : GGAttachNullPos (Matrix.transpose CartanMatrix.F₄) 3 :=
  ⟨fun | none => 1 | some i => ![2, 4, 3, 2] i, by decide +kernel, by decide +kernel⟩

@[expose] def GGIndefCellZero {Λ : Type} (C : Matrix Λ Λ ℤ) (b : Λ) : Prop :=
  (∃ (n : ℕ) (hn : 5 ≤ n) (e : Fin n ≃ Λ), (∀ i j, C (e i) (e j) = CartanMatrix.D n i j) ∧
      (b = e ⟨n - 2, by omega⟩ ∨ b = e ⟨n - 1, by omega⟩)) ∨
  (∃ e : Fin 6 ≃ Λ, (∀ i j, C (e i) (e j) = CartanMatrix.E 6 i j) ∧
      (b = e 0 ∨ b = e 1 ∨ b = e 5)) ∨
  (∃ e : Fin 7 ≃ Λ, (∀ i j, C (e i) (e j) = CartanMatrix.E 7 i j) ∧
      (b = e 0 ∨ b = e 1 ∨ b = e 6)) ∨
  (∃ e : Fin 8 ≃ Λ, (∀ i j, C (e i) (e j) = CartanMatrix.E 8 i j) ∧
      (b = e 0 ∨ b = e 1 ∨ b = e 7)) ∨
  (∃ e : Fin 4 ≃ Λ, ((∀ i j, C (e i) (e j) = CartanMatrix.F₄ i j) ∨
      (∀ i j, C (e i) (e j) = CartanMatrix.F₄ j i)) ∧ (b = e 0 ∨ b = e 3))

@[expose] def GGIndefCellOne {Λ : Type} (C : Matrix Λ Λ ℤ) (b : Λ) : Prop :=
  (∃ (n : ℕ) (hn : 9 ≤ n) (e : Fin n ≃ Λ), (∀ i j, C (e i) (e j) = CartanMatrix.D n i j) ∧
      (b = e ⟨n - 2, by omega⟩ ∨ b = e ⟨n - 1, by omega⟩)) ∨
  (∃ e : Fin 7 ≃ Λ, (∀ i j, C (e i) (e j) = CartanMatrix.E 7 i j) ∧ b = e 1) ∨
  (∃ e : Fin 8 ≃ Λ, (∀ i j, C (e i) (e j) = CartanMatrix.E 8 i j) ∧ (b = e 0 ∨ b = e 1))

private theorem trc_indefZero_D {Λ : Type} {C : Matrix Λ Λ ℤ} {b : Λ} (n : ℕ) (hn : 5 ≤ n)
    (e : Fin n ≃ Λ) (hC : ∀ i j, C (e i) (e j) = CartanMatrix.D n i j) (i : Fin n)
    (hi : i.val = n - 2 ∨ i.val = n - 1) (hb : b = e i) : GGIndefCellZero C b := by
  rcases hi with hi | hi
  · refine Or.inl ⟨n, hn, e, hC, Or.inl ?_⟩
    rw [hb]
    exact congrArg e (Fin.ext (by omega))
  · refine Or.inl ⟨n, hn, e, hC, Or.inr ?_⟩
    rw [hb]
    exact congrArg e (Fin.ext (by omega))

private theorem trc_indefZero_E6 {Λ : Type} {C : Matrix Λ Λ ℤ} {b : Λ} (e : Fin 6 ≃ Λ)
    (hC : ∀ i j, C (e i) (e j) = CartanMatrix.E 6 i j)
    (hb : b = e 0 ∨ b = e 1 ∨ b = e 5) : GGIndefCellZero C b :=
  Or.inr (Or.inl ⟨e, hC, hb⟩)

private theorem trc_indefZero_E7 {Λ : Type} {C : Matrix Λ Λ ℤ} {b : Λ} (e : Fin 7 ≃ Λ)
    (hC : ∀ i j, C (e i) (e j) = CartanMatrix.E 7 i j)
    (hb : b = e 0 ∨ b = e 1 ∨ b = e 6) : GGIndefCellZero C b :=
  Or.inr (Or.inr (Or.inl ⟨e, hC, hb⟩))

private theorem trc_indefZero_E8 {Λ : Type} {C : Matrix Λ Λ ℤ} {b : Λ} (e : Fin 8 ≃ Λ)
    (hC : ∀ i j, C (e i) (e j) = CartanMatrix.E 8 i j)
    (hb : b = e 0 ∨ b = e 1 ∨ b = e 7) : GGIndefCellZero C b :=
  Or.inr (Or.inr (Or.inr (Or.inl ⟨e, hC, hb⟩)))

private theorem trc_indefZero_F4 {Λ : Type} {C : Matrix Λ Λ ℤ} {b : Λ} (e : Fin 4 ≃ Λ)
    (hC : ∀ i j, C (e i) (e j) = CartanMatrix.F₄ i j) (hb : b = e 0 ∨ b = e 3) :
    GGIndefCellZero C b :=
  Or.inr (Or.inr (Or.inr (Or.inr ⟨e, Or.inl hC, hb⟩)))

private theorem trc_indefZero_F4T {Λ : Type} {C : Matrix Λ Λ ℤ} {b : Λ} (e : Fin 4 ≃ Λ)
    (hC : ∀ i j, C (e i) (e j) = CartanMatrix.F₄ j i) (hb : b = e 0 ∨ b = e 3) :
    GGIndefCellZero C b :=
  Or.inr (Or.inr (Or.inr (Or.inr ⟨e, Or.inr hC, hb⟩)))

private theorem trc_indefOne_D {Λ : Type} {C : Matrix Λ Λ ℤ} {b : Λ} (n : ℕ) (hn : 9 ≤ n)
    (e : Fin n ≃ Λ) (hC : ∀ i j, C (e i) (e j) = CartanMatrix.D n i j) (i : Fin n)
    (hi : i.val = n - 2 ∨ i.val = n - 1) (hb : b = e i) : GGIndefCellOne C b := by
  rcases hi with hi | hi
  · refine Or.inl ⟨n, hn, e, hC, Or.inl ?_⟩
    rw [hb]
    exact congrArg e (Fin.ext (by omega))
  · refine Or.inl ⟨n, hn, e, hC, Or.inr ?_⟩
    rw [hb]
    exact congrArg e (Fin.ext (by omega))

private theorem trc_indefOne_E7 {Λ : Type} {C : Matrix Λ Λ ℤ} {b : Λ} (e : Fin 7 ≃ Λ)
    (hC : ∀ i j, C (e i) (e j) = CartanMatrix.E 7 i j) (hb : b = e 1) : GGIndefCellOne C b :=
  Or.inr (Or.inl ⟨e, hC, hb⟩)

private theorem trc_indefOne_E8 {Λ : Type} {C : Matrix Λ Λ ℤ} {b : Λ} (e : Fin 8 ≃ Λ)
    (hC : ∀ i j, C (e i) (e j) = CartanMatrix.E 8 i j) (hb : b = e 0 ∨ b = e 1) :
    GGIndefCellOne C b :=
  Or.inr (Or.inr ⟨e, hC, hb⟩)

theorem ggAttachNullPos_of_affineCell {Λ : Type} [Fintype Λ] [DecidableEq Λ] {C : Matrix Λ Λ ℤ}
    {b : Λ} (h : GGForkAffineCell C b) : GGAttachNullPos C b := by
  rcases h with ⟨e, hC, hb⟩ | ⟨e, hC, hb⟩ | ⟨e, hC, hb⟩ | ⟨e, hC, hb⟩ |
    ⟨e, hC, hb⟩ | ⟨e, hC, hb⟩ | ⟨e, hC, hb⟩ | ⟨e, hC, hb⟩
  · exact trc_attachNullPos_of_equiv e hC hb trc_nullPos_E6_1
  · exact trc_attachNullPos_of_equiv e hC hb trc_nullPos_E7_0
  · exact trc_attachNullPos_of_equiv e hC hb trc_nullPos_E8_7
  · exact trc_attachNullPos_of_equiv e hC hb trc_nullPos_D8_7
  · exact trc_attachNullPos_of_equiv e hC hb trc_nullPos_F4_0
  · exact trc_attachNullPos_of_equiv e hC hb trc_nullPos_F4_3
  · exact trc_attachNullPos_of_equiv e hC hb trc_nullPos_F4T_0
  · exact trc_attachNullPos_of_equiv e hC hb trc_nullPos_F4T_3

private theorem trc_cell_A {Λ : Type} [Fintype Λ] [DecidableEq Λ] {C : Matrix Λ Λ ℤ} {b c : Λ}
    {n : ℕ} (hn : 1 ≤ n) (e : Fin n ≃ Λ)
    (hA : ∀ i j, C (e i) (e j) = CartanMatrix.A n i j) (hF : GGForkMatrix C b c) :
    GGAttachWeyl C c ∧ GGAttachWeyl C b := by
  rcases n with _ | _ | _ | n
  · omega
  · exfalso
    refine (hF.leafPos e hA).1 (Fin.ext ?_)
    have h1 := (e.symm b).isLt
    have h2 := (e.symm c).isLt
    omega
  · rcases ggLeafPos_A2 (hF.leafPos e hA) with ⟨hi, hk⟩ | ⟨hi, hk⟩
    · have hb : b = e 0 := by rw [← hi, e.apply_symm_apply]
      have hc : c = e 1 := by rw [← hk, e.apply_symm_apply]
      refine ⟨?_, ?_⟩
      · exact trc_attachWeyl_of_equiv e hA (k' := (1 : Fin 2)) hc trc_attachWeyl_A2_1
      · exact trc_attachWeyl_of_equiv e hA (k' := (0 : Fin 2)) hb trc_attachWeyl_A2_0
    · have hb : b = e 1 := by rw [← hi, e.apply_symm_apply]
      have hc : c = e 0 := by rw [← hk, e.apply_symm_apply]
      refine ⟨?_, ?_⟩
      · exact trc_attachWeyl_of_equiv e hA (k' := (0 : Fin 2)) hc trc_attachWeyl_A2_0
      · exact trc_attachWeyl_of_equiv e hA (k' := (1 : Fin 2)) hb trc_attachWeyl_A2_1
  · rcases ggLeafPos_A (by omega) (hF.leafPos e hA) with ⟨hi, _⟩ | ⟨hi, _⟩
    · have hb0 : b = e 0 := by
        have h0 : e.symm b = (0 : Fin (n + 3)) := Fin.ext hi
        rw [← h0]
        exact (e.apply_symm_apply b).symm
      have hrev : ∀ a b' : Fin (n + 3),
          C ((Fin.revPerm.trans e) a) ((Fin.revPerm.trans e) b') = CartanMatrix.A (n + 3) a b' := by
        intro a b'
        simp only [Equiv.trans_apply, Fin.revPerm_apply]
        exact (hA (Fin.rev a) (Fin.rev b')).trans (cartanMatrix_A_rev (n + 3) a b')
      have hb_rev : (Fin.revPerm.trans e) (Fin.last (n + 2)) = b := by
        simp only [Equiv.trans_apply, Fin.revPerm_apply, Fin.rev_last]
        exact hb0.symm
      obtain ⟨m, e', hm, hb', hC'⟩ : GGForkShapeA C b :=
        ⟨n + 2, Fin.revPerm.trans e, by omega, hb_rev, hrev⟩
      have hc' : c = e' ⟨m - 1, by omega⟩ :=
        eq_of_forkShapeA (by omega) hb' hC'
          (by rw [hF.bL c hF.ne.symm, if_pos rfl])
      exact ⟨by rw [hc']; exact exists_weyl_ggAttachCartan_forkShapeA_c hm hC',
        by rw [← hb']; exact exists_weyl_ggAttachCartan_forkShapeA_b hC'⟩
    · have hb_last : e (Fin.last (n + 2)) = b := by
        have hsymm : e.symm b = Fin.last (n + 2) := Fin.ext (by simp only [Fin.val_last]; omega)
        rw [← hsymm, e.apply_symm_apply]
      obtain ⟨m, e', hm, hb', hC'⟩ : GGForkShapeA C b :=
        ⟨n + 2, e, by omega, hb_last, hA⟩
      have hc' : c = e' ⟨m - 1, by omega⟩ :=
        eq_of_forkShapeA (by omega) hb' hC'
          (by rw [hF.bL c hF.ne.symm, if_pos rfl])
      exact ⟨by rw [hc']; exact exists_weyl_ggAttachCartan_forkShapeA_c hm hC',
        by rw [← hb']; exact exists_weyl_ggAttachCartan_forkShapeA_b hC'⟩

private theorem trc_cell_BC {Λ : Type} [Fintype Λ] [DecidableEq Λ] {C : Matrix Λ Λ ℤ} {b c : Λ}
    {n : ℕ} (hn : 2 ≤ n) (e : Fin n ≃ Λ)
    (hC : (∀ i j, C (e i) (e j) = CartanMatrix.B n i j) ∨
      (∀ i j, C (e i) (e j) = CartanMatrix.C n i j))
    (hF : GGForkMatrix C b c) : GGForkShapeBCD C b :=
  ggForkCell_BC hn e hC hF

private theorem trc_cell_D {Λ : Type} [Fintype Λ] [DecidableEq Λ] {C : Matrix Λ Λ ℤ} {b c : Λ}
    {n : ℕ} (hn4 : 4 ≤ n) (e : Fin n ≃ Λ)
    (hD : ∀ i j, C (e i) (e j) = CartanMatrix.D n i j) (hF : GGForkMatrix C b c)
    (hSB : ¬ GGForkShapeBCD C b) :
    (GGAttachWeyl C c ∨ GGIndefCellZero C b) ∧
      (GGAttachWeyl C b ∨ GGAttachNullPos C b ∨ GGIndefCellOne C b) := by
  rcases eq_or_lt_of_le hn4 with h4 | h5
  · subst h4
    obtain ⟨_, hi⟩ := ggLeafPos_D4 (hF.leafPos e hD)
    have hb : b = e 0 ∨ b = e 2 ∨ b = e 3 := by
      have h0 : b = e (e.symm b) := (e.apply_symm_apply b).symm
      rcases hi with hi | hi | hi
      · left; rw [hi] at h0; exact h0
      · right; left; rw [hi] at h0; exact h0
      · right; right; rw [hi] at h0; exact h0
    exact (hSB (ggForkShapeBCD_D4 e hD hb)).elim
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 5 := ⟨n - 5, by omega⟩
    rcases ggLeafPos_D m (hF.leafPos e hD) with ⟨hi, _⟩ | ⟨hsp, _⟩
    · exfalso
      have heb : e 0 = b := by
        have h0 : e.symm b = (0 : Fin (m + 5)) := Fin.ext hi
        rw [← h0]
        exact e.apply_symm_apply b
      exact hSB ⟨m + 2, e, heb, Or.inr (Or.inr ⟨by omega, hD⟩)⟩
    · have hb : b = e (e.symm b) := (e.apply_symm_apply b).symm
      have hb3 : b = e ⟨m + 3, by omega⟩ ∨ b = e ⟨m + 4, by omega⟩ := by
        rcases hsp with hsp | hsp
        · left
          have h0 : e.symm b = (⟨m + 3, by omega⟩ : Fin (m + 5)) := Fin.ext hsp
          rw [hb, h0]
        · right
          have h0 : e.symm b = (⟨m + 4, by omega⟩ : Fin (m + 5)) := Fin.ext hsp
          rw [hb, h0]
      refine ⟨Or.inr (trc_indefZero_D (m + 5) (by omega) e hD (e.symm b)
        (by rcases hsp with hsp | hsp <;> omega) hb), ?_⟩
      rcases m with _ | _ | _ | _ | m'
      · rcases hb3 with hb3 | hb3
        · exact Or.inl (trc_attachWeyl_of_equiv e hD (k' := (⟨3, by norm_num⟩ : Fin 5)) hb3
            trc_attachWeyl_D5_spin3)
        · exact Or.inl (trc_attachWeyl_of_equiv e hD (k' := (⟨4, by norm_num⟩ : Fin 5)) hb3
            trc_attachWeyl_D5_spin4)
      · rcases hb3 with hb3 | hb3
        · exact Or.inl (trc_attachWeyl_of_equiv e hD (k' := (⟨4, by norm_num⟩ : Fin 6)) hb3
            trc_attachWeyl_D6_spin4)
        · exact Or.inl (trc_attachWeyl_of_equiv e hD (k' := (⟨5, by norm_num⟩ : Fin 6)) hb3
            trc_attachWeyl_D6_spin5)
      · rcases hb3 with hb3 | hb3
        · exact Or.inl (trc_attachWeyl_of_equiv e hD (k' := (⟨5, by norm_num⟩ : Fin 7)) hb3
            trc_attachWeyl_D7_spin5)
        · exact Or.inl (trc_attachWeyl_of_equiv e hD (k' := (⟨6, by norm_num⟩ : Fin 7)) hb3
            trc_attachWeyl_D7_spin6)
      · exact Or.inr (Or.inl (ggAttachNullPos_of_affineCell (ggForkAffineCell_D8 e hD hb3)))
      · exact Or.inr (Or.inr (trc_indefOne_D (m' + 9) (by omega) e hD (e.symm b)
          (by rcases hsp with hsp | hsp <;> omega) hb))

private theorem trc_cell_E6 {Λ : Type} [Fintype Λ] [DecidableEq Λ] {C : Matrix Λ Λ ℤ} {b c : Λ}
    (e : Fin 6 ≃ Λ) (hC : ∀ i j, C (e i) (e j) = CartanMatrix.E 6 i j)
    (hF : GGForkMatrix C b c) :
    (GGAttachWeyl C c ∨ GGIndefCellZero C b) ∧
      (GGAttachWeyl C b ∨ GGAttachNullPos C b ∨ GGIndefCellOne C b) := by
  rcases ggLeafPos_E6 (hF.leafPos e hC) with ⟨hi, _⟩ | ⟨hi, _⟩ | ⟨hi, _⟩
  · have hb : b = e 0 := by rw [← hi, e.apply_symm_apply]
    exact ⟨Or.inr (trc_indefZero_E6 e hC (Or.inl hb)),
      Or.inl (trc_attachWeyl_of_equiv e hC (k' := (0 : Fin 6)) hb trc_attachWeyl_E6_0)⟩
  · have hb : b = e 1 := by rw [← hi, e.apply_symm_apply]
    exact ⟨Or.inr (trc_indefZero_E6 e hC (Or.inr (Or.inl hb))),
      Or.inr (Or.inl (trc_attachNullPos_of_equiv e hC hb trc_nullPos_E6_1))⟩
  · have hb : b = e 5 := by rw [← hi, e.apply_symm_apply]
    exact ⟨Or.inr (trc_indefZero_E6 e hC (Or.inr (Or.inr hb))),
      Or.inl (trc_attachWeyl_of_equiv e hC (k' := (5 : Fin 6)) hb trc_attachWeyl_E6_5)⟩

private theorem trc_cell_E7 {Λ : Type} [Fintype Λ] [DecidableEq Λ] {C : Matrix Λ Λ ℤ} {b c : Λ}
    (e : Fin 7 ≃ Λ) (hC : ∀ i j, C (e i) (e j) = CartanMatrix.E 7 i j)
    (hF : GGForkMatrix C b c) :
    (GGAttachWeyl C c ∨ GGIndefCellZero C b) ∧
      (GGAttachWeyl C b ∨ GGAttachNullPos C b ∨ GGIndefCellOne C b) := by
  rcases ggLeafPos_E7 (hF.leafPos e hC) with ⟨hi, _⟩ | ⟨hi, _⟩ | ⟨hi, _⟩
  · have hb : b = e 0 := by rw [← hi, e.apply_symm_apply]
    exact ⟨Or.inr (trc_indefZero_E7 e hC (Or.inl hb)),
      Or.inr (Or.inl (trc_attachNullPos_of_equiv e hC hb trc_nullPos_E7_0))⟩
  · have hb : b = e 1 := by rw [← hi, e.apply_symm_apply]
    exact ⟨Or.inr (trc_indefZero_E7 e hC (Or.inr (Or.inl hb))),
      Or.inr (Or.inr (trc_indefOne_E7 e hC hb))⟩
  · have hb : b = e 6 := by rw [← hi, e.apply_symm_apply]
    exact ⟨Or.inr (trc_indefZero_E7 e hC (Or.inr (Or.inr hb))),
      Or.inl (trc_attachWeyl_of_equiv e hC (k' := (6 : Fin 7)) hb trc_attachWeyl_E7_6)⟩

private theorem trc_cell_E8 {Λ : Type} [Fintype Λ] [DecidableEq Λ] {C : Matrix Λ Λ ℤ} {b c : Λ}
    (e : Fin 8 ≃ Λ) (hC : ∀ i j, C (e i) (e j) = CartanMatrix.E 8 i j)
    (hF : GGForkMatrix C b c) :
    (GGAttachWeyl C c ∨ GGIndefCellZero C b) ∧
      (GGAttachWeyl C b ∨ GGAttachNullPos C b ∨ GGIndefCellOne C b) := by
  rcases ggLeafPos_E8 (hF.leafPos e hC) with ⟨hi, _⟩ | ⟨hi, _⟩ | ⟨hi, _⟩
  · have hb : b = e 0 := by rw [← hi, e.apply_symm_apply]
    exact ⟨Or.inr (trc_indefZero_E8 e hC (Or.inl hb)),
      Or.inr (Or.inr (trc_indefOne_E8 e hC (Or.inl hb)))⟩
  · have hb : b = e 1 := by rw [← hi, e.apply_symm_apply]
    exact ⟨Or.inr (trc_indefZero_E8 e hC (Or.inr (Or.inl hb))),
      Or.inr (Or.inr (trc_indefOne_E8 e hC (Or.inr hb)))⟩
  · have hb : b = e 7 := by rw [← hi, e.apply_symm_apply]
    exact ⟨Or.inr (trc_indefZero_E8 e hC (Or.inr (Or.inr hb))),
      Or.inr (Or.inl (trc_attachNullPos_of_equiv e hC hb trc_nullPos_E8_7))⟩

private theorem trc_cell_F4 {Λ : Type} [Fintype Λ] [DecidableEq Λ] {C : Matrix Λ Λ ℤ} {b c : Λ}
    (e : Fin 4 ≃ Λ) (hC : ∀ i j, C (e i) (e j) = CartanMatrix.F₄ i j)
    (hF : GGForkMatrix C b c) :
    (GGAttachWeyl C c ∨ GGIndefCellZero C b) ∧
      (GGAttachWeyl C b ∨ GGAttachNullPos C b ∨ GGIndefCellOne C b) := by
  rcases ggLeafPos_F4 (hF.leafPos e hC) with ⟨hi, _⟩ | ⟨hi, _⟩
  · have hb : b = e 0 := by rw [← hi, e.apply_symm_apply]
    exact ⟨Or.inr (trc_indefZero_F4 e hC (Or.inl hb)),
      Or.inr (Or.inl (trc_attachNullPos_of_equiv e hC hb trc_nullPos_F4_0))⟩
  · have hb : b = e 3 := by rw [← hi, e.apply_symm_apply]
    exact ⟨Or.inr (trc_indefZero_F4 e hC (Or.inr hb)),
      Or.inr (Or.inl (trc_attachNullPos_of_equiv e hC hb trc_nullPos_F4_3))⟩

private theorem trc_cell_F4T {Λ : Type} [Fintype Λ] [DecidableEq Λ] {C : Matrix Λ Λ ℤ} {b c : Λ}
    (e : Fin 4 ≃ Λ) (hC : ∀ i j, C (e i) (e j) = CartanMatrix.F₄ j i)
    (hF : GGForkMatrix C b c) :
    (GGAttachWeyl C c ∨ GGIndefCellZero C b) ∧
      (GGAttachWeyl C b ∨ GGAttachNullPos C b ∨ GGIndefCellOne C b) := by
  rcases ggLeafPos_F4T (hF.leafPos e hC) with ⟨hi, _⟩ | ⟨hi, _⟩
  · have hb : b = e 0 := by rw [← hi, e.apply_symm_apply]
    exact ⟨Or.inr (trc_indefZero_F4T e hC (Or.inl hb)),
      Or.inr (Or.inl (trc_attachNullPos_of_equiv e hC hb trc_nullPos_F4T_0))⟩
  · have hb : b = e 3 := by rw [← hi, e.apply_symm_apply]
    exact ⟨Or.inr (trc_indefZero_F4T e hC (Or.inr hb)),
      Or.inr (Or.inl (trc_attachNullPos_of_equiv e hC hb trc_nullPos_F4T_3))⟩

theorem ggForkRest_trichotomy {Λ : Type} [Fintype Λ] [DecidableEq Λ] {M : CoxeterMatrix Λ}
    {C : Matrix Λ Λ ℤ} {b c : Λ} (hM : GGIsWeylMatrix M) (hC : GGIntCartan M C)
    (hF : GGForkMatrix C b c) (hSB : ¬ GGForkShapeBCD C b) :
    (GGAttachWeyl C c ∨ GGIndefCellZero C b) ∧
      (GGAttachWeyl C b ∨ GGAttachNullPos C b ∨ GGIndefCellOne C b) := by
  rcases ggIntCartan_models hM hC with
    ⟨n, e, hn, hA | ⟨hn2, hB | hCC⟩ | ⟨hn4, hD⟩⟩ | ⟨e, hE6⟩ | ⟨e, hE7⟩ | ⟨e, hE8⟩ |
      ⟨e, hF4 | hF4T⟩ | ⟨e, hG | hGT⟩
  · obtain ⟨hbc, hbb⟩ := trc_cell_A hn e hA hF
    exact ⟨Or.inl hbc, Or.inl hbb⟩
  · exact (hSB (trc_cell_BC hn2 e (Or.inl hB) hF)).elim
  · exact (hSB (trc_cell_BC hn2 e (Or.inr hCC) hF)).elim
  · exact trc_cell_D hn4 e hD hF hSB
  · exact trc_cell_E6 e hE6 hF
  · exact trc_cell_E7 e hE7 hF
  · exact trc_cell_E8 e hE8 hF
  · exact trc_cell_F4 e hF4 hF
  · exact trc_cell_F4T e hF4T hF
  · exact (ggForkCell_G2 e (Or.inl hG) hF).elim
  · exact (ggForkCell_G2 e (Or.inr hGT) hF).elim

end CFSG.StandardType
