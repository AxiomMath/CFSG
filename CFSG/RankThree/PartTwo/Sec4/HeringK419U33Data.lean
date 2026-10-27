module

public import CFSG.Quasithin.Recognition.CertU33DcInputs

public section

namespace CFSG.RankThree.PartTwo.Sec4.HeringK419U33

open CFSG.Quasithin

@[expose] def pwP (w : List ℕ) : Equiv.Perm (Fin 28) := (w.map u33GenP).prod

@[expose] def genL : List (List ℕ) :=
  [[14, 20, 27, 6, 7, 5, 16, 19, 18, 1, 4, 2, 12, 15,
    13, 0, 26, 17, 23, 10, 25, 8, 11, 21, 24, 9, 3, 22],
   [7, 18, 11, 3, 25, 24, 6, 9, 0, 8, 20, 22, 17, 10,
    19, 4, 16, 5, 14, 1, 23, 15, 27, 13, 12, 21, 26, 2],
   [0, 10, 11, 12, 18, 16, 17, 14, 15, 13, 1, 2, 3, 9,
    7, 8, 5, 6, 4, 19, 20, 21, 27, 25, 26, 23, 24, 22],
   [1, 10, 26, 24, 21, 22, 5, 20, 9, 25, 0, 3, 2, 15,
    7, 23, 17, 27, 4, 19, 14, 18, 6, 13, 11, 8, 12, 16],
   [12, 13, 27, 7, 16, 8, 1, 18, 20, 26, 0, 11, 10, 6,
    21, 9, 23, 25, 3, 17, 5, 24, 2, 4, 14, 19, 15, 22]]

theorem genL_rep : ∀ i : Fin 5, RepL (genL.getD i []) (u33GenP i) := by decide +kernel

@[expose] def pwL (w : List ℕ) : List ℕ :=
  w.foldr (fun i acc => compL (genL.getD i []) acc) (List.range 28)

theorem repL_pwP : ∀ w : List ℕ, (∀ i ∈ w, i < 5) → RepL (pwL w) (pwP w)
  | [], _ => by simpa [pwL, pwP] using repL_one 28
  | i :: w, hw => by
      have hi : i < 5 := hw i (List.mem_cons_self ..)
      have ih := repL_pwP w fun j hj => hw j (List.mem_cons_of_mem _ hj)
      have h := repL_mul (genL_rep ⟨i, hi⟩) ih
      simpa [pwL, pwP] using h

theorem mul_eq_of_lists {w₁ w₂ w₃ w₄ : List ℕ} (h₁ : ∀ i ∈ w₁, i < 5) (h₂ : ∀ i ∈ w₂, i < 5)
    (h₃ : ∀ i ∈ w₃, i < 5) (h₄ : ∀ i ∈ w₄, i < 5)
    (h : compL (pwL w₁) (pwL w₂) = compL (pwL w₃) (pwL w₄)) :
    pwP w₁ * pwP w₂ = pwP w₃ * pwP w₄ :=
  eq_of_repL (repL_mul (repL_pwP w₁ h₁) (repL_pwP w₂ h₂))
    (h ▸ repL_mul (repL_pwP w₃ h₃) (repL_pwP w₄ h₄))

theorem mul_ne_of_lists {w₁ w₂ w₃ w₄ : List ℕ} (h₁ : ∀ i ∈ w₁, i < 5) (h₂ : ∀ i ∈ w₂, i < 5)
    (h₃ : ∀ i ∈ w₃, i < 5) (h₄ : ∀ i ∈ w₄, i < 5)
    (h : compL (pwL w₁) (pwL w₂) ≠ compL (pwL w₃) (pwL w₄)) :
    pwP w₁ * pwP w₂ ≠ pwP w₃ * pwP w₄ :=
  ne_of_repL_ne (repL_mul (repL_pwP w₁ h₁) (repL_pwP w₂ h₂))
    (repL_mul (repL_pwP w₃ h₃) (repL_pwP w₄ h₄)) h

theorem pwP_eq_one_of_list {w : List ℕ} (hw : ∀ i ∈ w, i < 5) (h : pwL w = List.range 28) :
    pwP w = 1 :=
  eq_of_repL (repL_pwP w hw) (h ▸ repL_one 28)

@[expose] def wX' : List ℕ := [2, 4, 3, 2, 4, 1]

@[expose] def Ew : List (List ℕ) :=
  [[], [0, 4, 0, 3, 4, 4, 3, 4, 2], [0, 4, 3, 0, 4, 3, 4], [2, 4, 3, 2, 4, 1],
   [1, 3, 2, 4, 3, 4, 4, 3, 2], [2, 3, 4, 3, 2, 4, 1, 3], [4, 3, 0, 4, 4],
   [0, 3, 3, 4, 3, 4, 4, 3], [1, 3, 4, 3, 4, 4, 3, 3], [3], [4, 3, 4, 3, 4, 3, 4, 0],
   [0, 4, 3, 0, 4, 3, 4, 3], [3, 2, 4, 3, 2, 4, 1], [0, 2, 3, 4, 3, 4, 4, 3, 2],
   [2, 4, 3, 2, 4, 1, 3], [1, 3, 4, 3, 4, 4], [4, 3, 0, 4, 4, 3], [0, 3, 3, 4, 3, 4, 4, 3, 3],
   [3, 3], [3, 4, 3, 4, 3, 4, 3, 4, 0], [0, 1, 3, 3, 4, 3, 4, 3, 4], [2, 3, 4, 3, 2, 4, 1],
   [2, 4, 3, 0, 4, 4, 3, 2], [3, 2, 4, 3, 2, 4, 1, 3], [0, 3, 3, 4, 3, 4, 4],
   [1, 3, 4, 3, 4, 4, 3], [4, 3, 0, 4, 4, 3, 3]]

@[expose] def Epm (i : Fin 27) : Equiv.Perm (Fin 28) := pwP (Ew.getD i [])

@[expose] def conjTable : List (List ℕ × Bool) :=
  [([], false), ([0, 2, 3, 4], true), ([0, 0, 3, 4], true), ([0, 1, 4, 0], false),
   ([0, 1, 4, 0, 3, 3], false), ([0, 1, 4, 0, 3], false), ([4, 4, 0, 4], false),
   ([4, 4, 0, 4, 3], false), ([0, 1, 4, 0, 3, 2], false), ([], false),
   ([2, 4, 3, 2, 4, 1], false), ([4, 3, 0, 4, 4], false), ([0, 1, 1, 4, 3, 2, 4, 3], false),
   ([0, 1, 1, 4, 3, 2, 4], false), ([1, 4, 3, 4, 1, 3, 4, 0], false),
   ([1, 4, 3, 4, 1, 1, 3], false), ([1, 4, 1, 3, 2, 4, 3, 2], false), ([1, 4, 3, 4, 1, 1], false),
   ([2], false), ([2, 4, 3, 0, 4, 4], false), ([4, 3, 2, 4, 1], false),
   ([1, 4, 1, 3, 2, 4, 3, 3], false), ([1, 4, 1, 3, 2, 4, 3], false), ([1, 4, 1, 3, 2, 4], false),
   ([4, 3, 3, 4, 3, 4, 4, 1], false), ([4, 4, 3, 4, 0, 0], false), ([4, 4, 3, 4, 0, 0, 3], false)]

theorem Ew_lt : ∀ w ∈ Ew, ∀ i ∈ w, i < 5 := by decide

theorem wX'_lt : ∀ i ∈ wX', i < 5 := by decide

theorem conjTable_lt : ∀ p ∈ conjTable, ∀ i ∈ p.1, i < 5 := by decide

theorem Ew_getD_lt (i : Fin 27) : ∀ j ∈ Ew.getD i [], j < 5 := by
  have h : ∀ i : Fin 27, Ew.getD i [] ∈ Ew := by decide
  exact Ew_lt _ (h i)

theorem table_getD_lt (i : Fin 27) : ∀ j ∈ (conjTable.getD i ([], false)).1, j < 5 := by
  have h : ∀ i : Fin 27, conjTable.getD i ([], false) ∈ conjTable := by decide
  exact conjTable_lt _ (h i)

private theorem lt_three : ∀ i ∈ [3], i < 5 := by decide

private theorem lt_four : ∀ i ∈ [4], i < 5 := by decide

theorem Epm_closed_lists : ∀ i : Fin 27,
    (∃ j : Fin 27, compL (pwL (Ew.getD i [])) (pwL [3]) = pwL (Ew.getD j [])) ∧
    (∃ j : Fin 27, compL (pwL (Ew.getD i [])) (pwL wX') = pwL (Ew.getD j [])) ∧
    (∃ j : Fin 27, compL (pwL (Ew.getD j [])) (pwL [3]) = pwL (Ew.getD i [])) ∧
    (∃ j : Fin 27, compL (pwL (Ew.getD j [])) (pwL wX') = pwL (Ew.getD i [])) := by
  decide +kernel

theorem Epm_cube_lists : ∀ i : Fin 27,
    compL (pwL (Ew.getD i [])) (compL (pwL (Ew.getD i [])) (pwL (Ew.getD i []))) =
      List.range 28 := by
  decide +kernel

theorem x_x'_ne_lists : compL (pwL [3]) (pwL wX') ≠ compL (pwL wX') (pwL [3]) := by
  decide +kernel

theorem Epm_table_lists : ∀ i : Fin 27, pwL (Ew.getD i []) = List.range 28 ∨
    compL (pwL (conjTable.getD i ([], false)).1) (pwL (Ew.getD i [])) =
      compL (pwL (if (conjTable.getD i ([], false)).2 then [4] else [3]))
        (pwL (conjTable.getD i ([], false)).1) := by
  decide +kernel

theorem Epm_closed : ∀ i : Fin 27,
    (∃ j : Fin 27, Epm i * pwP [3] = Epm j) ∧ (∃ j : Fin 27, Epm i * pwP wX' = Epm j) ∧
    (∃ j : Fin 27, Epm j * pwP [3] = Epm i) ∧ (∃ j : Fin 27, Epm j * pwP wX' = Epm i) := by
  intro i
  obtain ⟨⟨j₁, h₁⟩, ⟨j₂, h₂⟩, ⟨j₃, h₃⟩, ⟨j₄, h₄⟩⟩ := Epm_closed_lists i
  have hrep : ∀ k : Fin 27, RepL (pwL (Ew.getD k [])) (Epm k) := fun k =>
    repL_pwP _ (Ew_getD_lt k)
  have hx : RepL (pwL [3]) (pwP [3]) := repL_pwP _ lt_three
  have hx' : RepL (pwL wX') (pwP wX') := repL_pwP _ wX'_lt
  refine ⟨⟨j₁, eq_of_repL (repL_mul (hrep i) hx) (h₁ ▸ hrep j₁)⟩,
    ⟨j₂, eq_of_repL (repL_mul (hrep i) hx') (h₂ ▸ hrep j₂)⟩,
    ⟨j₃, eq_of_repL (repL_mul (hrep j₃) hx) (h₃ ▸ hrep i)⟩,
    ⟨j₄, eq_of_repL (repL_mul (hrep j₄) hx') (h₄ ▸ hrep i)⟩⟩

theorem Epm_cube : ∀ i : Fin 27, Epm i ^ 3 = 1 := by
  intro i
  have hrep : RepL (pwL (Ew.getD i [])) (Epm i) := repL_pwP _ (Ew_getD_lt i)
  have h := repL_mul hrep (repL_mul hrep hrep)
  rw [Epm_cube_lists i] at h
  rw [pow_three]
  exact eq_of_repL h (repL_one 28)

theorem x_x'_ne : pwP [3] * pwP wX' ≠ pwP wX' * pwP [3] :=
  mul_ne_of_lists lt_three wX'_lt wX'_lt lt_three x_x'_ne_lists

theorem Epm_table : ∀ i : Fin 27, Epm i = 1 ∨
    pwP (conjTable.getD i ([], false)).1 * Epm i =
      pwP (if (conjTable.getD i ([], false)).2 then [4] else [3]) *
        pwP (conjTable.getD i ([], false)).1 := by
  intro i
  rcases Epm_table_lists i with h | h
  · exact Or.inl (pwP_eq_one_of_list (Ew_getD_lt i) h)
  · refine Or.inr (mul_eq_of_lists (table_getD_lt i) (Ew_getD_lt i) ?_ (table_getD_lt i) h)
    split_ifs
    · exact lt_four
    · exact lt_three

end CFSG.RankThree.PartTwo.Sec4.HeringK419U33
