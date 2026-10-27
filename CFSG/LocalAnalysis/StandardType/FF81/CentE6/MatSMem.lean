module

public import CFSG.LocalAnalysis.StandardType.FF81.CentE6.Std

public section

namespace CFSG.StandardType.FF81.CentE6

open scoped MatrixGroups

private lemma zmod_two_eq_zero_or_one (a : ZMod 2) : a = 0 ∨ a = 1 := by
  revert a
  decide

private lemma ite_zero_mul (a b : ZMod 2) : (if a = 0 then 0 else b) = b * a := by
  rcases zmod_two_eq_zero_or_one a with h | h
  · simp [h]
  · subst h; simp

private lemma add_add_self (a b : ZMod 2) : a + b + a = b := by
  rw [add_comm a b, add_assoc, CharTwo.add_self_eq_zero, add_zero]

private lemma elem_coe_of_ne (i j : Fin 6) (hij : i ≠ j) :
    ((elem i j : SL(6, ZMod 2)) : Matrix (Fin 6) (Fin 6) (ZMod 2)) =
      1 + Matrix.single i j 1 := by
  simp only [elem, dif_neg hij]
  exact Matrix.SpecialLinearGroup.transvection_coe hij 1

private def rowSupp (s : Finset (Fin 6)) : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  ∑ j ∈ s, Matrix.single (0 : Fin 6) j 1

private def colSupp (s : Finset (Fin 6)) : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  ∑ i ∈ s, Matrix.single i (5 : Fin 6) 1

private lemma rowSupp_apply (s : Finset (Fin 6)) (i j : Fin 6) :
    rowSupp s i j = if i = 0 ∧ j ∈ s then 1 else 0 := by
  classical
  rw [rowSupp, Matrix.sum_apply]
  simp only [Matrix.single_apply]
  by_cases hi : i = 0
  · subst hi
    by_cases hj : j ∈ s
    · rw [if_pos ⟨rfl, hj⟩]
      rw [Finset.sum_eq_single j (fun b _ hbj => by simp [hbj]) (fun hj' => absurd hj hj')]
      simp
    · rw [if_neg (by simp [hj])]
      apply Finset.sum_eq_zero
      intro b hb
      have hbj : b ≠ j := fun h => hj (h ▸ hb)
      simp [hbj]
  · rw [if_neg (by simp [hi])]
    apply Finset.sum_eq_zero
    intro b _
    simp [show (0 : Fin 6) ≠ i from fun h => hi h.symm]

private lemma colSupp_apply (s : Finset (Fin 6)) (i j : Fin 6) :
    colSupp s i j = if i ∈ s ∧ j = 5 then 1 else 0 := by
  classical
  rw [colSupp, Matrix.sum_apply]
  simp only [Matrix.single_apply]
  by_cases hj : j = 5
  · subst hj
    by_cases hi : i ∈ s
    · rw [if_pos ⟨hi, rfl⟩]
      rw [Finset.sum_eq_single i (fun b _ hbi => by simp [hbi]) (fun hi' => absurd hi hi')]
      simp
    · rw [if_neg (by simp [hi])]
      apply Finset.sum_eq_zero
      intro b hb
      have hbi : b ≠ i := fun h => hi (h ▸ hb)
      simp [hbi]
  · rw [if_neg (by simp [hj])]
    apply Finset.sum_eq_zero
    intro b _
    simp [show (5 : Fin 6) ≠ j from fun h => hj h.symm]

private lemma rowSupp_diag (s : Finset (Fin 6)) (hs : ∀ j ∈ s, j ≠ 0) (i : Fin 6) :
    (1 + rowSupp s) i i = 1 := by
  by_cases hi : i = 0
  · subst hi
    have h0s : (0 : Fin 6) ∉ s := fun h => hs 0 h rfl
    simp [Matrix.add_apply, rowSupp_apply, h0s]
  · have h : ¬ (i = 0 ∧ i ∈ s) := fun h => hi h.1
    simp [Matrix.add_apply, rowSupp_apply, h]

private lemma rowSupp_upper (s : Finset (Fin 6)) : (1 + rowSupp s).IsUpperTriangular := by
  intro i j hji
  change j < i at hji
  have hij : i ≠ j := ne_of_gt hji
  have hnot : ¬ (i = 0 ∧ j ∈ s) := by
    rintro ⟨rfl, -⟩
    exact absurd hji (by simp)
  simp [Matrix.add_apply, rowSupp_apply, hij, hnot]

private lemma rowElt_det (s : Finset (Fin 6)) (hs : ∀ j ∈ s, j ≠ 0) :
    (1 + rowSupp s).det = 1 := by
  rw [Matrix.det_of_isUpperTriangular (rowSupp_upper s)]
  exact Finset.prod_eq_one (fun i _ => rowSupp_diag s hs i)

private def rowElt (s : Finset (Fin 6)) (hs : ∀ j ∈ s, j ≠ 0) : SL(6, ZMod 2) :=
  ⟨1 + rowSupp s, rowElt_det s hs⟩

private lemma rowElt_coe (s : Finset (Fin 6)) (hs : ∀ j ∈ s, j ≠ 0) :
    ((rowElt s hs : SL(6, ZMod 2)) : Matrix (Fin 6) (Fin 6) (ZMod 2)) = 1 + rowSupp s := rfl

private lemma colSupp_diag (s : Finset (Fin 6)) (hs : ∀ i ∈ s, i ≠ 5) (i : Fin 6) :
    (1 + colSupp s) i i = 1 := by
  by_cases hi : i = 5
  · subst hi
    have h5s : (5 : Fin 6) ∉ s := fun h => hs 5 h rfl
    simp [Matrix.add_apply, colSupp_apply, h5s]
  · have h : ¬ (i ∈ s ∧ i = 5) := fun h => hi h.2
    simp [Matrix.add_apply, colSupp_apply, h]

private lemma colSupp_upper (s : Finset (Fin 6)) : (1 + colSupp s).IsUpperTriangular := by
  intro i j hji
  change j < i at hji
  have hij : i ≠ j := ne_of_gt hji
  have hnot : ¬ (i ∈ s ∧ j = 5) := by
    rintro ⟨-, h5⟩
    rw [h5] at hji
    have hi6 := i.isLt
    omega
  simp [Matrix.add_apply, colSupp_apply, hij, hnot]

private lemma colElt_det (s : Finset (Fin 6)) (hs : ∀ i ∈ s, i ≠ 5) :
    (1 + colSupp s).det = 1 := by
  rw [Matrix.det_of_isUpperTriangular (colSupp_upper s)]
  exact Finset.prod_eq_one (fun i _ => colSupp_diag s hs i)

private def colElt (s : Finset (Fin 6)) (hs : ∀ i ∈ s, i ≠ 5) : SL(6, ZMod 2) :=
  ⟨1 + colSupp s, colElt_det s hs⟩

private lemma colElt_coe (s : Finset (Fin 6)) (hs : ∀ i ∈ s, i ≠ 5) :
    ((colElt s hs : SL(6, ZMod 2)) : Matrix (Fin 6) (Fin 6) (ZMod 2)) = 1 + colSupp s := rfl

private def rowShape (g : SL(6, ZMod 2)) : Prop :=
  g.1 0 0 = 1 ∧ ∀ i j : Fin 6, i ≠ 0 → g.1 i j = if i = j then 1 else 0

private lemma fin_one_le_of_ne_zero {j : Fin 6} (hj : j ≠ 0) : 1 ≤ j.val := by
  rcases Nat.eq_zero_or_pos j.val with h | h
  · exact absurd (Fin.ext (by simpa using h)) hj
  · exact h

private lemma rowShape_one : rowShape (1 : SL(6, ZMod 2)) := by
  refine ⟨?_, ?_⟩
  · simp
  · intro i j _
    simp [Matrix.SpecialLinearGroup.coe_one, Matrix.one_apply]

private lemma rowShape_mul (x y : SL(6, ZMod 2)) (hx : rowShape x) (hy : rowShape y) :
    rowShape (x * y) := by
  obtain ⟨hx0, hx⟩ := hx
  obtain ⟨hy0, hy⟩ := hy
  refine ⟨?_, ?_⟩
  · rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_six]
    simp [hx0, hy0, hy]
  · intro i j hi
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_six]
    fin_cases i <;> simp_all

private lemma rowShape_sq (x : SL(6, ZMod 2)) (hx : rowShape x) : x * x = 1 := by
  obtain ⟨hx0, hx⟩ := hx
  apply Subtype.ext
  ext i j
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one, Matrix.mul_apply,
    Fin.sum_univ_six]
  fin_cases i <;> fin_cases j <;> simp [hx0, hx, CharTwo.add_self_eq_zero]

private lemma rowShape_inv (x : SL(6, ZMod 2)) (hx : rowShape x) : rowShape x⁻¹ := by
  rw [inv_eq_of_mul_eq_one_right (rowShape_sq x hx)]
  exact hx

private lemma elem_rowShape (j : Fin 6) (hj : 1 ≤ j.val) : rowShape (elem 0 j) := by
  have hj0 : (0 : Fin 6) ≠ j := by
    intro h; rw [← h] at hj; simp at hj
  rw [rowShape, elem_coe_of_ne 0 j hj0]
  refine ⟨?_, ?_⟩
  · simp [Matrix.add_apply, show j ≠ 0 from fun h => hj0 h.symm]
  · intro i j' hi
    rw [Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]
    simp [show (0 : Fin 6) ≠ i from fun h => hi h.symm]

private def SoneSub : Subgroup SL(6, ZMod 2) where
  carrier := {g | rowShape g}
  mul_mem' := fun hx hy => rowShape_mul _ _ hx hy
  one_mem' := rowShape_one
  inv_mem' := fun hx => rowShape_inv _ hx

private lemma Sone_le_SoneSub : Sone ≤ SoneSub := by
  rw [Sone, Subgroup.closure_le]
  rintro g ⟨j, hj, rfl⟩
  exact elem_rowShape j hj

private lemma rowElt_mem (s : Finset (Fin 6)) :
    ∀ hs : ∀ j ∈ s, j ≠ 0, rowElt s hs ∈ Sone := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      intro hs
      have h1 : rowElt (∅ : Finset (Fin 6)) hs = 1 := by
        apply Subtype.ext
        rw [rowElt_coe]
        simp [rowSupp]
      rw [h1]; exact Sone.one_mem
  | insert j t hjt ih =>
      intro hs
      have hj0 : j ≠ 0 := hs j (Finset.mem_insert_self j t)
      have ht : ∀ k ∈ t, k ≠ 0 := fun k hk => hs k (Finset.mem_insert_of_mem hk)
      have hstep : rowElt (insert j t) hs = elem 0 j * rowElt t ht := by
        apply Subtype.ext
        rw [rowElt_coe, Matrix.SpecialLinearGroup.coe_mul, rowElt_coe,
          elem_coe_of_ne 0 j (Ne.symm hj0)]
        have hrow : rowSupp (insert j t) = Matrix.single (0 : Fin 6) j 1 + rowSupp t := by
          simp [rowSupp, Finset.sum_insert hjt]
        have hzero : Matrix.single (0 : Fin 6) j 1 * rowSupp t = 0 := by
          rw [rowSupp, Finset.mul_sum]
          apply Finset.sum_eq_zero
          intro k _
          rw [Matrix.single_mul_single_of_ne (h := hj0)]
        rw [hrow, add_mul, one_mul, mul_add, mul_one, hzero, add_zero]
        abel
      rw [hstep]
      exact Sone.mul_mem (by
        rw [Sone]
        exact Subgroup.subset_closure ⟨j, fin_one_le_of_ne_zero hj0, rfl⟩) (ih ht)

private lemma SoneSub_le_Sone : SoneSub ≤ Sone := by
  intro g hg
  have hg' : rowShape g := hg
  obtain ⟨hg0, hg⟩ := hg'
  classical
  let s : Finset (Fin 6) := Finset.univ.filter (fun j : Fin 6 => 1 ≤ j.val ∧ g.1 0 j ≠ 0)
  have hs : ∀ j ∈ s, j ≠ 0 := by
    intro j hj h0
    have h := (Finset.mem_filter.mp hj).2.1
    rw [h0] at h
    exact absurd h (by simp)
  have heq : rowElt s hs = g := by
    apply Subtype.ext
    rw [rowElt_coe]
    ext i j
    rw [Matrix.add_apply, Matrix.one_apply, rowSupp_apply]
    by_cases hi : i = 0
    · subst hi
      by_cases hj : j = 0
      · subst hj
        have h0s : (0 : Fin 6) ∉ s := fun h => hs 0 h rfl
        simp [h0s, hg0]
      · have hjs : j ∈ s ↔ g.1 0 j ≠ 0 := by
          simp only [s, Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨fun h => h.2, fun h => ⟨fin_one_le_of_ne_zero hj, h⟩⟩
        have hcond : ¬ ((0 : Fin 6) = j) := fun h => hj h.symm
        rw [if_neg hcond]
        simp only [true_and, zero_add]
        by_cases h : j ∈ s
        · rw [if_pos h]
          rcases zmod_two_eq_zero_or_one (g.1 0 j) with h0 | h1
          · exact absurd h0 (hjs.mp h)
          · exact h1.symm
        · rw [if_neg h]
          exact (not_not.mp (hjs.not.mp h)).symm
    · have hcond : ¬ (i = 0 ∧ j ∈ s) := fun h => hi h.1
      rw [if_neg hcond, add_zero]
      exact (hg i j hi).symm
  rw [← heq]
  exact rowElt_mem s hs

private def colShape (g : SL(6, ZMod 2)) : Prop :=
  g.1 5 5 = 1 ∧ ∀ i j : Fin 6, j ≠ 5 → g.1 i j = if i = j then 1 else 0

private lemma colShape_one : colShape (1 : SL(6, ZMod 2)) := by
  refine ⟨?_, ?_⟩
  · simp
  · intro i j _
    simp [Matrix.SpecialLinearGroup.coe_one, Matrix.one_apply]

private lemma colShape_mul (x y : SL(6, ZMod 2)) (hx : colShape x) (hy : colShape y) :
    colShape (x * y) := by
  obtain ⟨hx5, hx⟩ := hx
  obtain ⟨hy5, hy⟩ := hy
  refine ⟨?_, ?_⟩
  · rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_six]
    simp [hx5, hx, hy5]
  · intro i j hj
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_six]
    fin_cases j <;> simp_all

private lemma colShape_sq (x : SL(6, ZMod 2)) (hx : colShape x) : x * x = 1 := by
  obtain ⟨hx5, hx⟩ := hx
  apply Subtype.ext
  ext i j
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one, Matrix.mul_apply,
    Fin.sum_univ_six]
  fin_cases i <;> fin_cases j <;> simp [hx5, hx, CharTwo.add_self_eq_zero]

private lemma colShape_inv (x : SL(6, ZMod 2)) (hx : colShape x) : colShape x⁻¹ := by
  rw [inv_eq_of_mul_eq_one_right (colShape_sq x hx)]
  exact hx

private lemma elem_colShape (i : Fin 6) (hi : i.val ≤ 4) : colShape (elem i 5) := by
  have hi5 : i ≠ 5 := by
    intro h; rw [h] at hi; simp at hi
  rw [colShape, elem_coe_of_ne i 5 hi5]
  refine ⟨?_, ?_⟩
  · simp [Matrix.add_apply, hi5]
  · intro i' j hj
    rw [Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]
    simp [show (5 : Fin 6) ≠ j from fun h => hj h.symm]

private def SsixSub : Subgroup SL(6, ZMod 2) where
  carrier := {g | colShape g}
  mul_mem' := fun hx hy => colShape_mul _ _ hx hy
  one_mem' := colShape_one
  inv_mem' := fun hx => colShape_inv _ hx

private lemma Ssix_le_SsixSub : Ssix ≤ SsixSub := by
  rw [Ssix, Subgroup.closure_le]
  rintro g ⟨i, hi, rfl⟩
  exact elem_colShape i hi

private lemma colElt_mem (s : Finset (Fin 6)) :
    ∀ hs : ∀ i ∈ s, i ≠ 5, colElt s hs ∈ Ssix := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      intro hs
      have h1 : colElt (∅ : Finset (Fin 6)) hs = 1 := by
        apply Subtype.ext
        rw [colElt_coe]
        simp [colSupp]
      rw [h1]; exact Ssix.one_mem
  | insert i t hit ih =>
      intro hs
      have hi5 : i ≠ 5 := hs i (Finset.mem_insert_self i t)
      have ht : ∀ k ∈ t, k ≠ 5 := fun k hk => hs k (Finset.mem_insert_of_mem hk)
      have hstep : colElt (insert i t) hs = elem i 5 * colElt t ht := by
        apply Subtype.ext
        rw [colElt_coe, Matrix.SpecialLinearGroup.coe_mul, colElt_coe, elem_coe_of_ne i 5 hi5]
        have hcol : colSupp (insert i t) = Matrix.single i (5 : Fin 6) 1 + colSupp t := by
          simp [colSupp, Finset.sum_insert hit]
        have hzero : Matrix.single i (5 : Fin 6) 1 * colSupp t = 0 := by
          rw [colSupp, Finset.mul_sum]
          apply Finset.sum_eq_zero
          intro k hk
          rw [Matrix.single_mul_single_of_ne (h := Ne.symm (ht k hk))]
        rw [hcol, add_mul, one_mul, mul_add, mul_one, hzero, add_zero]
        abel
      rw [hstep]
      exact Ssix.mul_mem (by
        rw [Ssix]
        refine Subgroup.subset_closure ⟨i, ?_, rfl⟩
        have h6 : i.val < 6 := i.isLt
        have hne : i.val ≠ 5 := fun h => hi5 (Fin.ext h)
        omega) (ih ht)

private lemma SsixSub_le_Ssix : SsixSub ≤ Ssix := by
  intro g hg
  have hg' : colShape g := hg
  obtain ⟨hg5, hg⟩ := hg'
  classical
  let s : Finset (Fin 6) := Finset.univ.filter (fun i : Fin 6 => i.val ≤ 4 ∧ g.1 i 5 ≠ 0)
  have hs : ∀ i ∈ s, i ≠ 5 := by
    intro i hi h5
    have h := (Finset.mem_filter.mp hi).2.1
    rw [h5] at h
    exact absurd h (by simp)
  have heq : colElt s hs = g := by
    apply Subtype.ext
    rw [colElt_coe]
    ext i j
    rw [Matrix.add_apply, Matrix.one_apply, colSupp_apply]
    by_cases hj : j = 5
    · subst hj
      by_cases hi : i = 5
      · subst hi
        have h5s : (5 : Fin 6) ∉ s := fun h => hs 5 h rfl
        simp [h5s, hg5]
      · have his : i ∈ s ↔ g.1 i 5 ≠ 0 := by
          simp only [s, Finset.mem_filter, Finset.mem_univ, true_and]
          refine ⟨fun h => h.2, fun h => ⟨?_, h⟩⟩
          have h6 : i.val < 6 := i.isLt
          have hne : i.val ≠ 5 := fun h5 => hi (Fin.ext h5)
          omega
        rw [if_neg hi]
        simp only [and_true, zero_add]
        by_cases h : i ∈ s
        · rw [if_pos h]
          rcases zmod_two_eq_zero_or_one (g.1 i 5) with h0 | h1
          · exact absurd h0 (his.mp h)
          · exact h1.symm
        · rw [if_neg h]
          exact (not_not.mp (his.not.mp h)).symm
    · have hcond : ¬ (i ∈ s ∧ j = 5) := fun h => hj h.2
      rw [if_neg hcond, add_zero]
      exact (hg i j hj).symm
  rw [← heq]
  exact colElt_mem s hs

private def grpShape (g : SL(6, ZMod 2)) : Prop :=
  g.1 0 0 = 1 ∧ g.1 5 5 = 1 ∧
    (∀ i j : Fin 6, 1 ≤ i.val → i.val ≤ 4 → 1 ≤ j.val → j.val ≤ 4 →
      g.1 i j = if i = j then 1 else 0) ∧
    (∀ i : Fin 6, i ≠ 0 → g.1 i 0 = 0) ∧ (∀ j : Fin 6, j ≠ 5 → g.1 5 j = 0)

private lemma grpShape_mul (x y : SL(6, ZMod 2)) (hx : grpShape x) (hy : grpShape y) :
    grpShape (x * y) := by
  obtain ⟨hx00, hx55, hxmid, hx0, hx5⟩ := hx
  obtain ⟨hy00, hy55, hymid, hy0, hy5⟩ := hy
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply]
    rw [Finset.sum_eq_single 0]
    · rw [hx00, hy00, mul_one]
    · intro k _ hk; rw [hy0 k hk, mul_zero]
    · intro h; exact absurd (Finset.mem_univ 0) h
  · rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply]
    rw [Finset.sum_eq_single 5]
    · rw [hx55, hy55, mul_one]
    · intro k _ hk; rw [hx5 k hk, zero_mul]
    · intro h; exact absurd (Finset.mem_univ 5) h
  · intro i j hi1 hi2 hj1 hj2
    have hi0 : i ≠ 0 := fun h => by rw [h] at hi1; simp at hi1
    have hj5 : j ≠ 5 := fun h => by rw [h] at hj2; simp at hj2
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply]
    rw [Finset.sum_eq_single i]
    · rw [hxmid i i hi1 hi2 hi1 hi2, if_pos rfl, one_mul, hymid i j hi1 hi2 hj1 hj2]
    · intro k _ hk
      rcases eq_or_ne k 0 with rfl | hk0
      · rw [hx0 i hi0, zero_mul]
      rcases eq_or_ne k 5 with rfl | hk5
      · rw [hy5 j hj5, mul_zero]
      have hk1 : 1 ≤ k.val := fin_one_le_of_ne_zero hk0
      have hk4 : k.val ≤ 4 := by
        have h6 : k.val < 6 := k.isLt
        have hne : k.val ≠ 5 := fun h => hk5 (Fin.ext h)
        omega
      rw [hxmid i k hi1 hi2 hk1 hk4, if_neg (fun h => hk h.symm), zero_mul]
    · intro h; exact absurd (Finset.mem_univ i) h
  · intro i hi
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply]
    rw [Finset.sum_eq_single 0]
    · rw [hx0 i hi, zero_mul]
    · intro k _ hk; rw [hy0 k hk, mul_zero]
    · intro h; exact absurd (Finset.mem_univ 0) h
  · intro j hj
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply]
    rw [Finset.sum_eq_single 5]
    · rw [hy5 j hj, mul_zero]
    · intro k _ hk; rw [hx5 k hk, zero_mul]
    · intro h; exact absurd (Finset.mem_univ 5) h

private lemma grpShape_col_mul_row (y z : SL(6, ZMod 2)) (hy : colShape y) (hz : rowShape z) :
    grpShape (y * z) := by
  obtain ⟨hy5, hy⟩ := hy
  obtain ⟨hz0, hz⟩ := hz
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply]
    rw [Finset.sum_eq_single 0]
    · rw [hz0, mul_one]
      simpa using hy 0 0 (by decide)
    · intro k _ hk; rw [hz k 0 hk, if_neg hk, mul_zero]
    · intro h; exact absurd (Finset.mem_univ 0) h
  · rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply]
    rw [Finset.sum_eq_single 5]
    · rw [hy5, one_mul]
      simpa using hz 5 5 (by decide)
    · intro k _ hk; rw [hy 5 k hk, if_neg (fun h => hk h.symm), zero_mul]
    · intro h; exact absurd (Finset.mem_univ 5) h
  · intro i j hi1 hi2 hj1 hj2
    have hi0 : i ≠ 0 := fun h => by rw [h] at hi1; simp at hi1
    have hj0 : j ≠ 0 := fun h => by rw [h] at hj1; simp at hj1
    have hj5 : j ≠ 5 := fun h => by rw [h] at hj2; simp at hj2
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply]
    rw [Finset.sum_eq_single j]
    · rw [hz j j hj0, if_pos rfl, mul_one, hy i j hj5]
    · intro k _ hk
      rcases eq_or_ne k 0 with rfl | hk0
      · rw [hy i 0 (by decide), if_neg hi0, zero_mul]
      rcases eq_or_ne k 5 with rfl | hk5
      · rw [hz 5 j (by decide), if_neg (fun h => hj5 h.symm), mul_zero]
      have hk1 : 1 ≤ k.val := fin_one_le_of_ne_zero hk0
      have hk4 : k.val ≤ 4 := by
        have h6 : k.val < 6 := k.isLt
        have hne : k.val ≠ 5 := fun h => hk5 (Fin.ext h)
        omega
      rw [hz k j hk0, if_neg hk, mul_zero]
    · intro h; exact absurd (Finset.mem_univ j) h
  · intro i hi
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply]
    rw [Finset.sum_eq_single 0]
    · rw [hz0, mul_one, hy i 0 (by decide), if_neg hi]
    · intro k _ hk; rw [hz k 0 hk, if_neg hk, mul_zero]
    · intro h; exact absurd (Finset.mem_univ 0) h
  · intro j hj
    have hj5 : j ≠ 5 := hj
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply]
    rw [Finset.sum_eq_single 5]
    · rw [hy5, one_mul, hz 5 j (by decide), if_neg (fun h => hj5 h.symm)]
    · intro k _ hk; rw [hy 5 k hk, if_neg (fun h => hk h.symm), zero_mul]
    · intro h; exact absurd (Finset.mem_univ 5) h

private lemma one_add_rowSupp_mul_one_add_colSupp (s t : Finset (Fin 6)) :
    (1 + rowSupp s) * (1 + colSupp t) =
      1 + rowSupp s + colSupp t +
        (∑ k : Fin 6, (if k ∈ s then (1 : ZMod 2) else 0) * (if k ∈ t then 1 else 0)) •
          Matrix.single (0 : Fin 6) 5 1 := by
  have hcross : rowSupp s * colSupp t =
      (∑ k : Fin 6, (if k ∈ s then (1 : ZMod 2) else 0) * (if k ∈ t then 1 else 0)) •
        Matrix.single (0 : Fin 6) 5 1 := by
    ext i j
    rw [Matrix.mul_apply]
    by_cases hij : i = 0 ∧ j = 5
    · obtain ⟨rfl, rfl⟩ := hij
      rw [Matrix.smul_apply, Matrix.single_apply, if_pos ⟨rfl, rfl⟩, smul_eq_mul, mul_one]
      apply Finset.sum_congr rfl
      intro k _
      by_cases hks : k ∈ s <;> by_cases hkt : k ∈ t <;>
        simp [rowSupp_apply, colSupp_apply, hks, hkt]
    · rw [Matrix.smul_apply, Matrix.single_apply]
      have hne : ¬ (0 = i ∧ 5 = j) := by
        rintro ⟨h1, h2⟩
        exact hij ⟨h1.symm, h2.symm⟩
      rw [if_neg hne, smul_zero]
      apply Finset.sum_eq_zero
      intro k _
      by_cases hi : i = 0
      · subst hi
        have hj : j ≠ 5 := fun h => hij ⟨rfl, h⟩
        simp [colSupp_apply, hj]
      · simp [rowSupp_apply, hi]
  rw [show (1 + rowSupp s) * (1 + colSupp t) =
      1 + rowSupp s + colSupp t + rowSupp s * colSupp t by
    rw [add_mul, one_mul, mul_add, mul_one]; abel, hcross]

private lemma exists_sone_mul_ssix (g : SL(6, ZMod 2)) (hg : grpShape g) :
    ∃ a ∈ Sone, ∃ b ∈ Ssix, a * b = g := by
  obtain ⟨hg00, hg55, hgmid, hgcol0, hgrow5⟩ := hg
  classical
  let t : Finset (Fin 6) := Finset.univ.filter (fun i : Fin 6 => i.val ≤ 4 ∧ g.1 i 5 ≠ 0)
  let u5 : ZMod 2 := g.1 0 1 * g.1 1 5 + g.1 0 2 * g.1 2 5 +
    g.1 0 3 * g.1 3 5 + g.1 0 4 * g.1 4 5
  let v : Fin 6 → ZMod 2 := fun j => if j = 5 then u5 else g.1 0 j
  let s : Finset (Fin 6) := Finset.univ.filter (fun j : Fin 6 => 1 ≤ j.val ∧ v j ≠ 0)
  have ht : ∀ i ∈ t, i ≠ 5 := by
    intro i hi h5
    have h := (Finset.mem_filter.mp hi).2.1
    rw [h5] at h
    exact absurd h (by simp)
  have hs : ∀ j ∈ s, j ≠ 0 := by
    intro j hj h0
    have h := (Finset.mem_filter.mp hj).2.1
    rw [h0] at h
    exact absurd h (by simp)
  have hbmem : colElt t ht ∈ Ssix := colElt_mem t ht
  have hamem : rowElt s hs ∈ Sone := rowElt_mem s hs
  have hbmat : ((colElt t ht : SL(6, ZMod 2)) : Matrix (Fin 6) (Fin 6) (ZMod 2)) =
      1 + colSupp t := colElt_coe t ht
  have hamat : ((rowElt s hs : SL(6, ZMod 2)) : Matrix (Fin 6) (Fin 6) (ZMod 2)) =
      1 + rowSupp s := rowElt_coe s hs
  have hc : (∑ k : Fin 6, (if k ∈ s then (1 : ZMod 2) else 0) * (if k ∈ t then 1 else 0)) = u5 := by
    simp [s, t, v, u5, Fin.sum_univ_six, Finset.mem_filter, ite_zero_mul]
  refine ⟨rowElt s hs, hamem, colElt t ht, hbmem, ?_⟩
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, hamat, hbmat, one_add_rowSupp_mul_one_add_colSupp, hc]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [rowSupp_apply, colSupp_apply, Matrix.smul_apply, Matrix.single_apply,
      Matrix.add_apply, Matrix.one_apply, s, t, v, u5, Finset.mem_filter, Fin.reduceFinMk] <;>
    simp [ite_zero_mul, add_add_self, hg00, hg55, hgmid, hgcol0, hgrow5,
      CharTwo.add_self_eq_zero]

private def SgrpSub : Subgroup SL(6, ZMod 2) where
  carrier := {g | grpShape g}
  mul_mem' := fun hx hy => grpShape_mul _ _ hx hy
  one_mem' := ⟨by simp, by simp,
    (by intro i j _ _ _ _
        rw [Matrix.SpecialLinearGroup.coe_one, Matrix.one_apply]),
    (by intro i hi
        rw [Matrix.SpecialLinearGroup.coe_one, Matrix.one_apply]
        simp [hi]),
    (by intro j hj
        rw [Matrix.SpecialLinearGroup.coe_one, Matrix.one_apply]
        simp [show (5 : Fin 6) ≠ j from fun h => hj h.symm])⟩
  inv_mem' := by
    intro x hx
    obtain ⟨a, ha, b, hb, hab⟩ := exists_sone_mul_ssix x hx
    have hb' : colShape b := Ssix_le_SsixSub hb
    have ha' : rowShape a := Sone_le_SoneSub ha
    rw [← hab, mul_inv_rev]
    exact grpShape_col_mul_row b⁻¹ a⁻¹ (colShape_inv b hb') (rowShape_inv a ha')

private lemma Sone_le_SgrpSub : Sone ≤ SgrpSub := by
  intro g hg
  have hg' : rowShape g := Sone_le_SoneSub hg
  obtain ⟨h0, h1⟩ := hg'
  change grpShape g
  refine ⟨h0, ?_, ?_, ?_, ?_⟩
  · rw [h1 5 5 (by decide)]; simp
  · intro i j hi1 _ _ _
    exact h1 i j (fun h => by rw [h] at hi1; simp at hi1)
  · intro i hi; rw [h1 i 0 hi]; simp [hi]
  · intro j hj
    rw [h1 5 j (by decide)]
    simp [show (5 : Fin 6) ≠ j from fun h => hj h.symm]

private lemma Ssix_le_SgrpSub : Ssix ≤ SgrpSub := by
  intro g hg
  have hg' : colShape g := Ssix_le_SsixSub hg
  obtain ⟨h5, h1⟩ := hg'
  change grpShape g
  refine ⟨?_, h5, ?_, ?_, ?_⟩
  · rw [h1 0 0 (by decide)]; simp
  · intro i j _ _ _ hj2
    exact h1 i j (fun h => by rw [h] at hj2; simp at hj2)
  · intro i hi; rw [h1 i 0 (by decide)]; simp [hi]
  · intro j hj
    rw [h1 5 j hj]
    simp [show (5 : Fin 6) ≠ j from fun h => hj h.symm]

private lemma SgrpSub_le_Sgrp : SgrpSub ≤ Sgrp := by
  intro g hg
  have hg' : grpShape g := hg
  obtain ⟨a, ha, b, hb, hab⟩ := exists_sone_mul_ssix g hg'
  rw [← hab]
  exact Subgroup.mul_mem_sup ha hb

theorem mem_Sone_iff (g : SL(6, ZMod 2)) :
    g ∈ Sone ↔ g.1 0 0 = 1 ∧ ∀ i j : Fin 6, i ≠ 0 → g.1 i j = if i = j then 1 else 0 := by
  change g ∈ Sone ↔ rowShape g
  rw [show Sone = SoneSub from le_antisymm Sone_le_SoneSub SoneSub_le_Sone]
  exact Iff.rfl

theorem mem_Ssix_iff (g : SL(6, ZMod 2)) :
    g ∈ Ssix ↔ g.1 5 5 = 1 ∧ ∀ i j : Fin 6, j ≠ 5 → g.1 i j = if i = j then 1 else 0 := by
  change g ∈ Ssix ↔ colShape g
  rw [show Ssix = SsixSub from le_antisymm Ssix_le_SsixSub SsixSub_le_Ssix]
  exact Iff.rfl

theorem mem_Sgrp_iff (g : SL(6, ZMod 2)) :
    g ∈ Sgrp ↔ g.1 0 0 = 1 ∧ g.1 5 5 = 1 ∧
      (∀ i j : Fin 6, 1 ≤ i.val → i.val ≤ 4 → 1 ≤ j.val → j.val ≤ 4 →
        g.1 i j = if i = j then 1 else 0) ∧
      (∀ i : Fin 6, i ≠ 0 → g.1 i 0 = 0) ∧ (∀ j : Fin 6, j ≠ 5 → g.1 5 j = 0) := by
  change g ∈ Sgrp ↔ grpShape g
  rw [show Sgrp = SgrpSub from le_antisymm (sup_le Sone_le_SgrpSub Ssix_le_SgrpSub) SgrpSub_le_Sgrp]
  exact Iff.rfl

end CFSG.StandardType.FF81.CentE6
