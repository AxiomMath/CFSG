module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Quasithin.Vol2.Ch11SecB414MG

public section

namespace CFSG.Quasithin.H13.Ch4.B414.M

open Matrix

variable {F : Type} [Field F] [CharP F 2]

theorem two_eq_zero' : (2 : F) = 0 := CharTwo.two_eq_zero

@[expose] def Wp : AddSubgroup (Matrix (Fin 3) (Fin 3) F) where
  carrier := {M | ∀ i j : Fin 3, ¬ (i = 0 ∧ j ≠ 0) → M i j = 0}
  zero_mem' := fun _ _ _ => rfl
  add_mem' := fun ha hb i j h => by simp [ha i j h, hb i j h]
  neg_mem' := fun ha i j h => by simp [ha i j h]

@[expose] def W2 : AddSubgroup (Matrix (Fin 3) (Fin 3) F) where
  carrier := {M | M 0 0 = 0 ∧ M 1 0 = 0 ∧ M 2 0 = 0 ∧ M 1 2 = 0 ∧ M 2 1 = 0 ∧ M 1 1 = M 2 2}
  zero_mem' := by simp
  add_mem' := by
    rintro a b ⟨a1, a2, a3, a4, a5, a6⟩ ⟨b1, b2, b3, b4, b5, b6⟩
    simp_all
  neg_mem' := by
    rintro a ⟨a1, a2, a3, a4, a5, a6⟩
    simp_all

@[expose] def W2a : AddSubgroup (Matrix (Fin 3) (Fin 3) F) where
  carrier := {M | M ∈ (W2 : AddSubgroup (Matrix (Fin 3) (Fin 3) F)) ∧ (M 1 1 = 0 ∨ M 1 1 = 1)}
  zero_mem' := ⟨W2.zero_mem, Or.inl rfl⟩
  add_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨W2.add_mem ha hb, ?_⟩
    simp only [Matrix.add_apply]
    rcases ha' with h | h <;> rcases hb' with h' | h' <;> simp [h, h', two_eq_zero' (F := F),
      one_add_one_eq_two]
  neg_mem' := by
    rintro a ⟨ha, ha'⟩
    refine ⟨W2.neg_mem ha, ?_⟩
    simp only [Matrix.neg_apply]
    rcases ha' with h | h <;> simp [h, CharTwo.neg_eq]

@[expose] def W3 : AddSubgroup (Matrix (Fin 3) (Fin 3) F) where
  carrier := {M | M 0 0 = 0 ∧ M 1 0 = 0 ∧ M 2 0 = 0 ∧ M 1 1 = M 2 2}
  zero_mem' := by simp
  add_mem' := by
    rintro a b ⟨a1, a2, a3, a4⟩ ⟨b1, b2, b3, b4⟩
    simp_all
  neg_mem' := by
    rintro a ⟨a1, a2, a3, a4⟩
    simp_all

@[expose] def W4 : AddSubgroup (Matrix (Fin 3) (Fin 3) F) where
  carrier := {M | M.trace = 0 ∧ M 1 0 = 0 ∧ M 2 0 = 0}
  zero_mem' := by simp
  add_mem' := by
    rintro a b ⟨a1, a2, a3⟩ ⟨b1, b2, b3⟩
    simp_all [Matrix.trace_add]
  neg_mem' := by
    rintro a ⟨a1, a2, a3⟩
    simp_all [Matrix.trace_neg]

@[expose] def W4a : AddSubgroup (Matrix (Fin 3) (Fin 3) F) where
  carrier := {M | M ∈ (W4 : AddSubgroup (Matrix (Fin 3) (Fin 3) F)) ∧ (M 0 0 = 0 ∨ M 0 0 = 1)}
  zero_mem' := ⟨W4.zero_mem, Or.inl rfl⟩
  add_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨W4.add_mem ha hb, ?_⟩
    simp only [Matrix.add_apply]
    rcases ha' with h | h <;> rcases hb' with h' | h' <;> simp [h, h', two_eq_zero' (F := F),
      one_add_one_eq_two]
  neg_mem' := by
    rintro a ⟨ha, ha'⟩
    refine ⟨W4.neg_mem ha, ?_⟩
    simp only [Matrix.neg_apply]
    rcases ha' with h | h <;> simp [h, CharTwo.neg_eq]

@[expose] def Wsl : AddSubgroup (Matrix (Fin 3) (Fin 3) F) where
  carrier := {M | M.trace = 0}
  zero_mem' := by simp
  add_mem' := by
    intro a b ha hb
    simp_all [Matrix.trace_add]
  neg_mem' := by
    intro a ha
    simp_all [Matrix.trace_neg]

theorem Wp_le_W2a : (Wp : AddSubgroup (Matrix (Fin 3) (Fin 3) F)) ≤ W2a := by
  intro M hM
  have h : ∀ i j : Fin 3, ¬ (i = 0 ∧ j ≠ 0) → M i j = 0 := hM
  exact ⟨⟨h 0 0 (by simp), h 1 0 (by simp), h 2 0 (by simp), h 1 2 (by simp), h 2 1 (by simp),
    by rw [h 1 1 (by simp), h 2 2 (by simp)]⟩, Or.inl (h 1 1 (by simp))⟩

theorem W2a_le_W2 : (W2a : AddSubgroup (Matrix (Fin 3) (Fin 3) F)) ≤ W2 := fun _ h => h.1

omit [CharP F 2] in
theorem W2_le_W3 : (W2 : AddSubgroup (Matrix (Fin 3) (Fin 3) F)) ≤ W3 :=
  fun _ ⟨h1, h2, h3, _, _, h6⟩ => ⟨h1, h2, h3, h6⟩

theorem W3_le_W4a : (W3 : AddSubgroup (Matrix (Fin 3) (Fin 3) F)) ≤ W4a := by
  rintro M ⟨h1, h2, h3, h4⟩
  refine ⟨⟨?_, h2, h3⟩, Or.inl h1⟩
  rw [Matrix.trace_fin_three, h1, h4]
  linear_combination M 2 2 * two_eq_zero' (F := F)

theorem W4a_le_W4 : (W4a : AddSubgroup (Matrix (Fin 3) (Fin 3) F)) ≤ W4 := fun _ h => h.1

omit [CharP F 2] in
theorem W4_le_Wsl : (W4 : AddSubgroup (Matrix (Fin 3) (Fin 3) F)) ≤ Wsl := fun _ h => h.1

section Cnj

variable {A : Matrix (Fin 3) (Fin 3) F} (h10 : A 1 0 = 0) (h20 : A 2 0 = 0) (hdet : A.det = 1)
include h10 h20

omit [CharP F 2] in
theorem Wp_cnj {M : Matrix (Fin 3) (Fin 3) F} (hM : M ∈ (Wp : AddSubgroup _)) :
    cnj A M ∈ (Wp : AddSubgroup (Matrix (Fin 3) (Fin 3) F)) := by
  have hM' : ∀ i j : Fin 3, ¬ (i = 0 ∧ j ≠ 0) → M i j = 0 := hM
  intro i j hij
  by_cases hi : i = 0
  · subst hi
    have hj : j = 0 := by
      by_contra hj
      exact hij ⟨rfl, hj⟩
    subst hj
    rw [cnj_row0_of_Wp hM' 0]
    simp [adjugate_fin_three, h10, h20]
  · exact cnj_block_of_Wp h10 h20 hM' i j hi

include hdet

omit [CharP F 2] in
theorem W2_cnj {M : Matrix (Fin 3) (Fin 3) F} (hM : M ∈ (W2 : AddSubgroup _)) :
    cnj A M ∈ (W2 : AddSubgroup (Matrix (Fin 3) (Fin 3) F)) ∧ cnj A M 1 1 = M 1 1 := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hM
  have hb := cnj_block_of_W2 h10 h20 hdet h2 h3 h4 h5 h6
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [cnj_00 h10 h20 h2 h3, h1]; ring
  · rw [cnj_col0 h10 h20 1 (by decide), h2, h3]; ring
  · rw [cnj_col0 h10 h20 2 (by decide), h2, h3]; ring
  · rw [hb 1 2 (by decide)]; simp
  · rw [hb 2 1 (by decide)]; simp
  · rw [hb 1 1 (by decide), hb 2 2 (by decide)]; simp
  · rw [hb 1 1 (by decide)]; simp

theorem W2a_cnj {M : Matrix (Fin 3) (Fin 3) F} (hM : M ∈ (W2a : AddSubgroup _)) :
    cnj A M ∈ (W2a : AddSubgroup (Matrix (Fin 3) (Fin 3) F)) := by
  obtain ⟨hW, h11⟩ := W2_cnj h10 h20 hdet hM.1
  exact ⟨hW, h11 ▸ hM.2⟩

omit [CharP F 2] in
theorem W2_cnj_sub {M : Matrix (Fin 3) (Fin 3) F} (hM : M ∈ (W2 : AddSubgroup _)) :
    cnj A M - M ∈ (Wp : AddSubgroup (Matrix (Fin 3) (Fin 3) F)) := by
  obtain ⟨⟨c1, c2, c3, c4, c5, c6⟩, c7⟩ := W2_cnj h10 h20 hdet hM
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hM
  intro i j hij
  simp only [Matrix.sub_apply]
  fin_cases i <;> fin_cases j <;> simp_all

theorem W3_cnj {M : Matrix (Fin 3) (Fin 3) F} (hM : M ∈ (W3 : AddSubgroup _)) :
    cnj A M ∈ (W3 : AddSubgroup (Matrix (Fin 3) (Fin 3) F)) := by
  obtain ⟨h1, h2, h3, h4⟩ := hM
  have h00 : cnj A M 0 0 = 0 := by rw [cnj_00 h10 h20 h2 h3, h1]; ring
  refine ⟨h00, ?_, ?_, ?_⟩
  · rw [cnj_col0 h10 h20 1 (by decide), h2, h3]; ring
  · rw [cnj_col0 h10 h20 2 (by decide), h2, h3]; ring
  · have ht := trace_cnj A M
    rw [hdet, one_mul, Matrix.trace_fin_three, Matrix.trace_fin_three, h00, h1, h4] at ht
    linear_combination ht + (M 2 2 - cnj A M 2 2) * two_eq_zero' (F := F)

omit [CharP F 2] in
theorem W4_cnj {M : Matrix (Fin 3) (Fin 3) F} (hM : M ∈ (W4 : AddSubgroup _)) :
    cnj A M ∈ (W4 : AddSubgroup (Matrix (Fin 3) (Fin 3) F)) ∧ cnj A M 0 0 = M 0 0 := by
  obtain ⟨h1, h2, h3⟩ := hM
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · rw [trace_cnj, hdet, h1, mul_zero]
  · rw [cnj_col0 h10 h20 1 (by decide), h2, h3]; ring
  · rw [cnj_col0 h10 h20 2 (by decide), h2, h3]; ring
  · rw [cnj_00 h10 h20 h2 h3]
    rw [det_of_par h10 h20] at hdet
    linear_combination M 0 0 * hdet

theorem W4a_cnj {M : Matrix (Fin 3) (Fin 3) F} (hM : M ∈ (W4a : AddSubgroup _)) :
    cnj A M ∈ (W4a : AddSubgroup (Matrix (Fin 3) (Fin 3) F)) := by
  obtain ⟨hW, h00⟩ := W4_cnj h10 h20 hdet hM.1
  exact ⟨hW, h00 ▸ hM.2⟩

theorem W4_cnj_sub {M : Matrix (Fin 3) (Fin 3) F} (hM : M ∈ (W4 : AddSubgroup _)) :
    cnj A M - M ∈ (W3 : AddSubgroup (Matrix (Fin 3) (Fin 3) F)) := by
  obtain ⟨⟨c1, c2, c3⟩, c4⟩ := W4_cnj h10 h20 hdet hM
  obtain ⟨h1, h2, h3⟩ := hM
  refine ⟨by simp [c4], by simp [c2, h2], by simp [c3, h3], ?_⟩
  simp only [Matrix.sub_apply]
  rw [Matrix.trace_fin_three] at c1 h1
  rw [c4] at c1
  linear_combination c1 - h1 + (M 2 2 - cnj A M 2 2) * two_eq_zero' (F := F)

end Cnj

omit [CharP F 2] in
theorem Wsl_cnj {A : Matrix (Fin 3) (Fin 3) F} (hdet : A.det = 1) {M : Matrix (Fin 3) (Fin 3) F}
    (hM : M ∈ (Wsl : AddSubgroup _)) :
    cnj A M ∈ (Wsl : AddSubgroup (Matrix (Fin 3) (Fin 3) F)) := by
  show (cnj A M).trace = 0
  rw [trace_cnj, hdet, one_mul]
  exact hM

end CFSG.Quasithin.H13.Ch4.B414.M
