module

public import CFSG.LocalAnalysis.StandardType.GGQTwoLin
public import CFSG.LocalAnalysis.StandardType.GGQTwoDWeyl

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Module QTwoLin

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private def ggQ2xA3_C : Matrix (Fin 3) (Fin 3) (ZMod 3) :=
  !![2, -1, 0; -1, 2, -1; 0, -1, 2]

private def ggQ2xA3_S (k : Fin 3) : Matrix (Fin 3) (Fin 3) (ZMod 3) :=
  1 - Matrix.single k k 1 * ggQ2xA3_C

private def ggQ2xA3a_mats : List (List ℕ) :=
  [[1, 0, 0, 0, 1, 0, 0, 0, 1],
   [2, 1, 0, 0, 1, 0, 0, 0, 1],
   [1, 0, 0, 1, 2, 1, 0, 0, 1],
   [1, 0, 0, 0, 1, 0, 0, 1, 2],
   [2, 1, 0, 2, 0, 1, 0, 0, 1],
   [2, 1, 0, 0, 1, 0, 0, 1, 2],
   [0, 2, 1, 1, 2, 1, 0, 0, 1],
   [1, 0, 0, 1, 2, 1, 1, 2, 0],
   [1, 0, 0, 1, 0, 2, 0, 1, 2],
   [0, 2, 1, 2, 0, 1, 0, 0, 1],
   [2, 1, 0, 2, 0, 1, 2, 0, 0],
   [2, 1, 0, 2, 1, 2, 0, 1, 2],
   [0, 2, 1, 1, 2, 1, 1, 2, 0],
   [1, 0, 0, 1, 0, 2, 1, 2, 0],
   [0, 0, 2, 1, 0, 2, 0, 1, 2],
   [0, 2, 1, 2, 0, 1, 2, 0, 0],
   [2, 1, 0, 2, 1, 2, 2, 0, 0],
   [0, 0, 2, 2, 1, 2, 0, 1, 2],
   [0, 2, 1, 0, 2, 0, 1, 2, 0],
   [0, 0, 2, 1, 0, 2, 1, 2, 0],
   [0, 2, 1, 0, 2, 0, 2, 0, 0],
   [0, 0, 2, 2, 1, 2, 2, 0, 0],
   [0, 0, 2, 0, 2, 0, 1, 2, 0],
   [0, 0, 2, 0, 2, 0, 2, 0, 0]]

private def ggQ2xA3a_parents : List (ℕ × ℕ) :=
  [(0, 0), (0, 1), (0, 2), (1, 1), (1, 2), (2, 0), (2, 2), (3, 1), (4, 0), (4, 2), (5, 1), (6, 2),
   (7, 1), (8, 0), (9, 2), (10, 1), (11, 0), (12, 1), (13, 0), (15, 1), (16, 0), (18, 0), (20, 0)]

private def ggQ2xA3a_tab : List (List ℕ) :=
  [[1, 2, 3], [0, 4, 5], [6, 0, 7], [5, 8, 0], [9, 1, 10], [3, 11, 1], [2, 9, 12], [12, 13, 2],
   [14, 3, 13], [4, 6, 15], [15, 16, 4], [17, 5, 16], [7, 18, 6], [19, 7, 8], [8, 17, 19],
   [10, 20, 9], [21, 10, 11], [11, 14, 21], [22, 12, 20], [13, 22, 14], [23, 15, 18], [16, 23, 17],
   [18, 19, 23], [20, 21, 22]]

private def ggQ2xA3a_toMat (l : List ℕ) : Matrix (Fin 3) (Fin 3) (ZMod 3) :=
  fun i j => ((l.getD (3 * (i : ℕ) + (j : ℕ)) 0 : ℕ) : ZMod 3)

private def ggQ2xA3a_Lm (i : ℕ) : Matrix (Fin 3) (Fin 3) (ZMod 3) :=
  ggQ2xA3a_toMat (ggQ2xA3a_mats.getD i [])

private def ggQ2xA3a_gen (k : ℕ) : Fin 3 := ⟨k % 3, Nat.mod_lt k (by decide)⟩

private def ggQ2xA3a_parentOf (i : ℕ) : ℕ × ℕ := ggQ2xA3a_parents.getD (i - 1) (0, 0)

private def ggQ2xA3a_chkOne : Bool := decide (ggQ2xA3a_Lm 0 = 1)

private def ggQ2xA3a_chkReach : Bool :=
  (List.range 24).all fun i =>
    (i == 0) || (decide (ggQ2xA3a_Lm i =
        ggQ2xA3_S (ggQ2xA3a_gen (ggQ2xA3a_parentOf i).2) * ggQ2xA3a_Lm (ggQ2xA3a_parentOf i).1) &&
      decide ((ggQ2xA3a_parentOf i).1 < i))

private def ggQ2xA3a_chkClosed : Bool :=
  (List.range 24).all fun i =>
    (List.range 3).all fun k =>
      decide (ggQ2xA3_S (ggQ2xA3a_gen k) * ggQ2xA3a_Lm i =
        ggQ2xA3a_Lm ((ggQ2xA3a_tab.getD i []).getD k 0))

private def ggQ2xA3a_chkTabLt : Bool :=
  (List.range 24).all fun i =>
    (List.range 3).all fun k => decide ((ggQ2xA3a_tab.getD i []).getD k 0 < 24)

private def ggQ2xA3a_chkDistinct : Bool :=
  (List.range 24).all fun i =>
    (List.range 24).all fun j => decide (ggQ2xA3a_Lm i = ggQ2xA3a_Lm j → i = j)

private theorem ggQ2xA3a_chkOne_eq : ggQ2xA3a_chkOne = true := by decide +kernel

private theorem ggQ2xA3a_chkReach_eq : ggQ2xA3a_chkReach = true := by decide +kernel

private theorem ggQ2xA3a_chkClosed_eq : ggQ2xA3a_chkClosed = true := by decide +kernel

private theorem ggQ2xA3a_chkTabLt_eq : ggQ2xA3a_chkTabLt = true := by decide +kernel

private theorem ggQ2xA3a_chkDistinct_eq : ggQ2xA3a_chkDistinct = true := by decide +kernel

private theorem ggQ2xA3a_Lm_zero : ggQ2xA3a_Lm 0 = 1 :=
  of_decide_eq_true ggQ2xA3a_chkOne_eq

private theorem ggQ2xA3a_reach_step (i : ℕ) (hi : i < 24) (h0 : i ≠ 0) :
    ggQ2xA3a_Lm i =
        ggQ2xA3_S (ggQ2xA3a_gen (ggQ2xA3a_parentOf i).2) * ggQ2xA3a_Lm (ggQ2xA3a_parentOf i).1 ∧
      (ggQ2xA3a_parentOf i).1 < i := by
  have h := (List.all_eq_true.mp ggQ2xA3a_chkReach_eq) i (List.mem_range.mpr hi)
  rw [Bool.or_eq_true] at h
  rcases h with h | h
  · exact absurd (beq_iff_eq.mp h) h0
  · rw [Bool.and_eq_true] at h
    exact ⟨of_decide_eq_true h.1, of_decide_eq_true h.2⟩

private theorem ggQ2xA3a_closed (i : ℕ) (hi : i < 24) (k : ℕ) (hk : k < 3) :
    ggQ2xA3_S (ggQ2xA3a_gen k) * ggQ2xA3a_Lm i =
      ggQ2xA3a_Lm ((ggQ2xA3a_tab.getD i []).getD k 0) :=
  of_decide_eq_true
    ((List.all_eq_true.mp ((List.all_eq_true.mp ggQ2xA3a_chkClosed_eq) i
      (List.mem_range.mpr hi))) k (List.mem_range.mpr hk))

private theorem ggQ2xA3a_tabLt (i : ℕ) (hi : i < 24) (k : ℕ) (hk : k < 3) :
    (ggQ2xA3a_tab.getD i []).getD k 0 < 24 :=
  of_decide_eq_true
    ((List.all_eq_true.mp ((List.all_eq_true.mp ggQ2xA3a_chkTabLt_eq) i
      (List.mem_range.mpr hi))) k (List.mem_range.mpr hk))

private theorem ggQ2xA3a_gen_eq (k : Fin 3) : ggQ2xA3a_gen (k : ℕ) = k := by
  ext
  exact Nat.mod_eq_of_lt k.isLt

private theorem ggQ2xA3a_closed_fin (i : ℕ) (hi : i < 24) (k : Fin 3) :
    ggQ2xA3_S k * ggQ2xA3a_Lm i =
      ggQ2xA3a_Lm ((ggQ2xA3a_tab.getD i []).getD (k : ℕ) 0) := by
  have h := ggQ2xA3a_closed i hi (k : ℕ) k.isLt
  rw [ggQ2xA3a_gen_eq k] at h
  exact h

private theorem ggQ2xA3a_distinct (i j : ℕ) (hi : i < 24) (hj : j < 24)
    (h : ggQ2xA3a_Lm i = ggQ2xA3a_Lm j) : i = j :=
  of_decide_eq_true
    ((List.all_eq_true.mp ((List.all_eq_true.mp ggQ2xA3a_chkDistinct_eq) i
      (List.mem_range.mpr hi))) j (List.mem_range.mpr hj)) h

private theorem ggQ2xA3a_reach (i : ℕ) (hi : i < 24) :
    ggQ2xA3a_Lm i ∈ Submonoid.closure (Set.range ggQ2xA3_S) := by
  revert hi
  refine Nat.strong_induction_on i ?_
  intro n ih hn
  rcases eq_or_ne n 0 with h0 | h0
  · rw [h0, ggQ2xA3a_Lm_zero]
    exact Submonoid.one_mem _
  · obtain ⟨heq, hlt⟩ := ggQ2xA3a_reach_step n hn h0
    rw [heq]
    exact Submonoid.mul_mem _
      (Submonoid.subset_closure (Set.mem_range_self (ggQ2xA3a_gen (ggQ2xA3a_parentOf n).2)))
      (ih (ggQ2xA3a_parentOf n).1 hlt (by omega))

private theorem ggQ2xA3a_closure_subset :
    (Submonoid.closure (Set.range ggQ2xA3_S) : Set (Matrix (Fin 3) (Fin 3) (ZMod 3))) ⊆
      Set.range (fun i : Fin 24 => ggQ2xA3a_Lm (i : ℕ)) := by
  intro x hx
  exact Submonoid.closure_induction_left
    (motive := fun x _ => x ∈ Set.range (fun i : Fin 24 => ggQ2xA3a_Lm (i : ℕ)))
    ⟨⟨0, by decide⟩, by simpa using ggQ2xA3a_Lm_zero⟩
    (by
      intro a ha b _ hb
      obtain ⟨k, rfl⟩ := ha
      obtain ⟨i, rfl⟩ := hb
      exact ⟨⟨(ggQ2xA3a_tab.getD (i : ℕ) []).getD (k : ℕ) 0,
          ggQ2xA3a_tabLt (i : ℕ) i.isLt (k : ℕ) k.isLt⟩,
        (ggQ2xA3a_closed_fin (i : ℕ) i.isLt k).symm⟩)
    hx

private theorem ggQ2xA3a_range_subset :
    Set.range (fun i : Fin 24 => ggQ2xA3a_Lm (i : ℕ)) ⊆
      (Submonoid.closure (Set.range ggQ2xA3_S) : Set (Matrix (Fin 3) (Fin 3) (ZMod 3))) := by
  rintro _ ⟨i, rfl⟩
  exact ggQ2xA3a_reach (i : ℕ) i.isLt

private theorem ggQ2xA3a_set_eq :
    (Submonoid.closure (Set.range ggQ2xA3_S) : Set (Matrix (Fin 3) (Fin 3) (ZMod 3))) =
      Set.range (fun i : Fin 24 => ggQ2xA3a_Lm (i : ℕ)) :=
  Set.Subset.antisymm ggQ2xA3a_closure_subset ggQ2xA3a_range_subset

private noncomputable def ggQ2xA3a_rangeEquiv :
    (Set.range (fun i : Fin 24 => ggQ2xA3a_Lm (i : ℕ))) ≃ Fin 24 where
  toFun x := Classical.choose (Set.mem_range.mp x.2)
  invFun i := ⟨ggQ2xA3a_Lm (i : ℕ), Set.mem_range_self i⟩
  left_inv x := by
    apply Subtype.ext
    exact Classical.choose_spec (Set.mem_range.mp x.2)
  right_inv i := by
    let f : Fin 24 → Matrix (Fin 3) (Fin 3) (ZMod 3) := fun i => ggQ2xA3a_Lm (i : ℕ)
    have hmem : f i ∈ Set.range f := Set.mem_range_self i
    let j : Fin 24 := Classical.choose (Set.mem_range.mp hmem)
    have hj : f j = f i := Classical.choose_spec (Set.mem_range.mp hmem)
    apply Fin.ext
    exact ggQ2xA3a_distinct (j : ℕ) (i : ℕ) j.isLt i.isLt hj

private theorem ggQ2xA3a_range_card :
    Nat.card (Set.range (fun i : Fin 24 => ggQ2xA3a_Lm (i : ℕ))) = 24 := by
  rw [Nat.card_congr ggQ2xA3a_rangeEquiv, Nat.card_fin]

private theorem ggQ2xA3_card :
    Nat.card (Submonoid.closure (Set.range ggQ2xA3_S)) = 24 := by
  change Nat.card (↥(Submonoid.closure (Set.range ggQ2xA3_S) :
    Set (Matrix (Fin 3) (Fin 3) (ZMod 3)))) = 24
  rw [ggQ2xA3a_set_eq]
  exact ggQ2xA3a_range_card

private theorem ggQ2xA3b_label2 (D : GGQ2Lin 3) {i j : D.ι} (hij : i ≠ j)
    (h : D.coxeter i j = 2) : (D.cartan i j : ZMod 3) = 0 := by
  rcases D.isCartan.2 i j hij with ⟨hm, h1, -⟩ | ⟨hm, -, -⟩ | ⟨hm, -, -, -⟩ | ⟨hm, -, -, -⟩
  · rw [h1]; norm_num
  · rw [h] at hm; omega
  · rw [h] at hm; omega
  · rw [h] at hm; omega

private theorem ggQ2xA3b_label3 (D : GGQ2Lin 3) {i j : D.ι} (hij : i ≠ j)
    (h : D.coxeter i j = 3) : (D.cartan i j : ZMod 3) = -1 := by
  rcases D.isCartan.2 i j hij with ⟨hm, -, -⟩ | ⟨hm, h1, -⟩ | ⟨hm, -, -, -⟩ | ⟨hm, -, -, -⟩
  · rw [h] at hm; omega
  · rw [h1]; norm_num
  · rw [h] at hm; omega
  · rw [h] at hm; omega

private theorem ggQ2xA3b_cox (D : GGQ2Lin 3) {m : ℕ} (e : Fin m ≃ D.ι)
    {M : CoxeterMatrix (Fin m)} (he : D.coxeter = M.reindex e) (i j : Fin m) :
    D.coxeter (e i) (e j) = M i j := by
  rw [he, CoxeterMatrix.reindex_apply]
  simp

private theorem ggQ2xA3b_mk (D : GGQ2Lin 3) (u v w : D.ι)
    (hu : u ≠ D.a) (hv : v ≠ D.a) (hw : w ≠ D.a)
    (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w)
    (hcov : ∀ k, k ≠ D.a → k = u ∨ k = v ∨ k = w)
    (huv1 : (D.cartan u v : ZMod 3) = -1) (hvu1 : (D.cartan v u : ZMod 3) = -1)
    (hvw1 : (D.cartan v w : ZMod 3) = -1) (hwv1 : (D.cartan w v : ZMod 3) = -1)
    (huw0 : (D.cartan u w : ZMod 3) = 0) (hwu0 : (D.cartan w u : ZMod 3) = 0) :
    ∃ f : Fin 3 ≃ {k // k ≠ D.a},
      ∀ i j, (D.cartan (f i).1 (f j).1 : ZMod 3) = ggQ2xA3_C i j := by
  let φ : Fin 3 → {k // k ≠ D.a} := ![⟨u, hu⟩, ⟨v, hv⟩, ⟨w, hw⟩]
  have hbij : Function.Bijective φ := by
    constructor
    · intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all [φ]
    · intro y
      rcases hcov y.1 y.2 with h | h | h
      · exact ⟨0, by apply Subtype.ext; simpa [φ] using h.symm⟩
      · exact ⟨1, by apply Subtype.ext; simpa [φ] using h.symm⟩
      · exact ⟨2, by apply Subtype.ext; simpa [φ] using h.symm⟩
  refine ⟨Equiv.ofBijective φ hbij, ?_⟩
  intro i j
  fin_cases i <;> fin_cases j <;> simp [φ, ggQ2xA3_C, Equiv.ofBijective_apply]
  all_goals
    first
      | exact huv1
      | exact hvu1
      | exact hvw1
      | exact hwv1
      | exact huw0
      | exact hwu0
      | (rw [D.isCartan.1 u]; norm_num)
      | (rw [D.isCartan.1 v]; norm_num)
      | (rw [D.isCartan.1 w]; norm_num)

private theorem ggQ2xA3b_case (D : GGQ2Lin 3) {m : ℕ} (e : Fin m ≃ D.ι)
    {M : CoxeterMatrix (Fin m)} (he : D.coxeter = M.reindex e) (x p q r : Fin m)
    (hpx : p ≠ x) (hqx : q ≠ x) (hrx : r ≠ x)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    (hperm : ∀ j, j ≠ x → j = p ∨ j = q ∨ j = r)
    (hda : D.a = e x)
    (hlab : M p q = 3 ∧ M q p = 3 ∧ M q r = 3 ∧ M r q = 3 ∧ M p r = 2 ∧ M r p = 2) :
    ∃ f : Fin 3 ≃ {k // k ≠ D.a},
      ∀ i j, (D.cartan (f i).1 (f j).1 : ZMod 3) = ggQ2xA3_C i j := by
  have hu : e p ≠ D.a := by rw [hda]; intro h; exact hpx (e.injective h)
  have hv : e q ≠ D.a := by rw [hda]; intro h; exact hqx (e.injective h)
  have hw : e r ≠ D.a := by rw [hda]; intro h; exact hrx (e.injective h)
  have hcov : ∀ k, k ≠ D.a → k = e p ∨ k = e q ∨ k = e r := by
    intro k hk
    have hk' : e.symm k ≠ x := by intro h; apply hk; rw [hda, ← h, Equiv.apply_symm_apply]
    rcases hperm (e.symm k) hk' with h | h | h
    · left; rw [← Equiv.apply_symm_apply e k, h]
    · right; left; rw [← Equiv.apply_symm_apply e k, h]
    · right; right; rw [← Equiv.apply_symm_apply e k, h]
  exact ggQ2xA3b_mk D (e p) (e q) (e r) hu hv hw (e.injective.ne hpq) (e.injective.ne hpr)
    (e.injective.ne hqr) hcov
    (ggQ2xA3b_label3 D (e.injective.ne hpq) ((ggQ2xA3b_cox D e he p q).trans hlab.1))
    (ggQ2xA3b_label3 D (e.injective.ne (fun h => hpq h.symm))
      ((ggQ2xA3b_cox D e he q p).trans hlab.2.1))
    (ggQ2xA3b_label3 D (e.injective.ne hqr) ((ggQ2xA3b_cox D e he q r).trans hlab.2.2.1))
    (ggQ2xA3b_label3 D (e.injective.ne (fun h => hqr h.symm))
      ((ggQ2xA3b_cox D e he r q).trans hlab.2.2.2.1))
    (ggQ2xA3b_label2 D (e.injective.ne hpr) ((ggQ2xA3b_cox D e he p r).trans hlab.2.2.2.2.1))
    (ggQ2xA3b_label2 D (e.injective.ne (fun h => hpr h.symm))
      ((ggQ2xA3b_cox D e he r p).trans hlab.2.2.2.2.2))

private theorem ggQ2xA3_cartan (D : GGQ2Lin 3) (e : Fin 4 ≃ D.ι)
    (h : (D.coxeter = (CoxeterMatrix.A 4).reindex e ∧ (D.a = e 0 ∨ D.a = e 3)) ∨
      (D.coxeter = (ggCoxeterMatrixD 4).reindex e ∧ (D.a = e 0 ∨ D.a = e 2 ∨ D.a = e 3)) ∨
      (D.coxeter = (CoxeterMatrix.B 4).reindex e ∧ D.a = e 3)) :
    ∃ f : Fin 3 ≃ {k // k ≠ D.a},
      ∀ i j, (D.cartan (f i).1 (f j).1 : ZMod 3) = ggQ2xA3_C i j := by
  rcases h with ⟨he, ha⟩ | ⟨he, ha⟩ | ⟨he, ha⟩
  · rcases ha with ha | ha
    · exact ggQ2xA3b_case D (M := CoxeterMatrix.A 4) e he 0 1 2 3
        (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)
        (by decide) ha (by decide)
    · exact ggQ2xA3b_case D (M := CoxeterMatrix.A 4) e he 3 0 1 2
        (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)
        (by decide) ha (by decide)
  · rcases ha with ha | ha | ha
    · exact ggQ2xA3b_case D (M := ggCoxeterMatrixD 4) e he 0 2 1 3
        (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)
        (by decide) ha (by rw [ggCoxeterMatrixD_apply]; decide)
    · exact ggQ2xA3b_case D (M := ggCoxeterMatrixD 4) e he 2 0 1 3
        (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)
        (by decide) ha (by rw [ggCoxeterMatrixD_apply]; decide)
    · exact ggQ2xA3b_case D (M := ggCoxeterMatrixD 4) e he 3 0 1 2
        (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)
        (by decide) ha (by rw [ggCoxeterMatrixD_apply]; decide)
  · exact ggQ2xA3b_case D (M := CoxeterMatrix.B 4) e he 3 0 1 2
      (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)
      (by decide) ha (by decide)

private def ggQ2xA3c_Cinv : Matrix (Fin 3) (Fin 3) (ZMod 3) :=
  !![0, 2, 1; 2, 1, 2; 1, 2, 0]

private theorem ggQ2xA3c_C_mul_Cinv : ggQ2xA3_C * ggQ2xA3c_Cinv = 1 := by decide

private theorem ggQ2xA3c_Cinv_mul_C : ggQ2xA3c_Cinv * ggQ2xA3_C = 1 := by decide

private noncomputable def ggQ2xA3c_Qvf (D : GGQ2Lin 3) (f : Fin 3 ≃ {k // k ≠ D.a})
    (c : Fin 3 → ZMod 3) : D.V :=
  ∑ i, c i • D.coroot (f i).1

private noncomputable def ggQ2xA3c_Qv (D : GGQ2Lin 3) (f : Fin 3 ≃ {k // k ≠ D.a}) :
    (Fin 3 → ZMod 3) →ₗ[ZMod 3] D.V where
  toFun := ggQ2xA3c_Qvf D f
  map_add' c d := by
    simp only [ggQ2xA3c_Qvf, Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' a c := by
    simp only [ggQ2xA3c_Qvf, Pi.smul_apply, Finset.smul_sum, smul_smul, smul_eq_mul,
      RingHom.id_apply]

private noncomputable def ggQ2xA3c_pi (D : GGQ2Lin 3) (f : Fin 3 ≃ {k // k ≠ D.a}) :
    D.V →ₗ[ZMod 3] (Fin 3 → ZMod 3) :=
  (Matrix.mulVecLin ggQ2xA3c_Cinv) ∘ₗ LinearMap.pi (fun i => D.root (f i).1)

private theorem ggQ2xA3c_pi_apply (D : GGQ2Lin 3) (f : Fin 3 ≃ {k // k ≠ D.a}) (v : D.V) :
    ggQ2xA3c_pi D f v = ggQ2xA3c_Cinv.mulVec (fun i => D.root (f i).1 v) := by
  rw [ggQ2xA3c_pi, LinearMap.comp_apply, Matrix.mulVecLin_apply]
  rfl

private theorem ggQ2xA3c_Qv_single (D : GGQ2Lin 3) (f : Fin 3 ≃ {k // k ≠ D.a})
    (i : Fin 3) (a : ZMod 3) :
    ggQ2xA3c_Qv D f (a • Pi.single i 1) = a • D.coroot (f i).1 := by
  rw [map_smul]
  congr 1
  show ggQ2xA3c_Qvf D f (Pi.single i 1) = D.coroot (f i).1
  simp only [ggQ2xA3c_Qvf]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    rw [Pi.single_eq_of_ne hj, zero_smul]
  · intro h; exact absurd (Finset.mem_univ i) h

private theorem ggQ2xA3c_alpha_Qv (D : GGQ2Lin 3) (f : Fin 3 ≃ {k // k ≠ D.a})
    (hf : ∀ i j, (D.cartan (f i).1 (f j).1 : ZMod 3) = ggQ2xA3_C i j)
    (c : Fin 3 → ZMod 3) (i : Fin 3) :
    D.root (f i).1 (ggQ2xA3c_Qv D f c) = (ggQ2xA3_C.mulVec c) i := by
  show (D.root (f i).1) (ggQ2xA3c_Qvf D f c) = (ggQ2xA3_C.mulVec c) i
  rw [ggQ2xA3c_Qvf, map_sum]
  rw [show (ggQ2xA3_C.mulVec c) i = ∑ j, ggQ2xA3_C i j * c j from rfl]
  apply Finset.sum_congr rfl
  intro j _
  rw [map_smul, D.pairing, hf i j]
  simp [smul_eq_mul, mul_comm]

private theorem ggQ2xA3c_C_mulVec_pi (D : GGQ2Lin 3) (f : Fin 3 ≃ {k // k ≠ D.a}) (v : D.V) :
    ggQ2xA3_C.mulVec (ggQ2xA3c_pi D f v) = fun i => D.root (f i).1 v := by
  rw [ggQ2xA3c_pi_apply, Matrix.mulVec_mulVec, ggQ2xA3c_C_mul_Cinv, Matrix.one_mulVec]

private theorem ggQ2xA3c_pi_Qv (D : GGQ2Lin 3) (f : Fin 3 ≃ {k // k ≠ D.a})
    (hf : ∀ i j, (D.cartan (f i).1 (f j).1 : ZMod 3) = ggQ2xA3_C i j)
    (c : Fin 3 → ZMod 3) :
    ggQ2xA3c_pi D f (ggQ2xA3c_Qv D f c) = c := by
  rw [ggQ2xA3c_pi_apply]
  have h : (fun i => D.root (f i).1 (ggQ2xA3c_Qv D f c)) = ggQ2xA3_C.mulVec c := by
    funext i; exact ggQ2xA3c_alpha_Qv D f hf c i
  rw [h, Matrix.mulVec_mulVec, ggQ2xA3c_Cinv_mul_C, Matrix.one_mulVec]

private theorem ggQ2xA3c_Qv_injective (D : GGQ2Lin 3) (f : Fin 3 ≃ {k // k ≠ D.a})
    (hf : ∀ i j, (D.cartan (f i).1 (f j).1 : ZMod 3) = ggQ2xA3_C i j) :
    Function.Injective (ggQ2xA3c_Qv D f) := by
  intro a b hab
  have h := congrArg (ggQ2xA3c_pi D f) hab
  rwa [ggQ2xA3c_pi_Qv D f hf a, ggQ2xA3c_pi_Qv D f hf b] at h

private def ggQ2xA3c_Pform (D : GGQ2Lin 3) (f : Fin 3 ≃ {k // k ≠ D.a})
    (g : D.V ≃ₗ[ZMod 3] D.V) (N : Matrix (Fin 3) (Fin 3) (ZMod 3)) : Prop :=
  ∀ v, g v = v + ggQ2xA3c_Qv D f ((N - 1).mulVec (ggQ2xA3c_pi D f v))

private theorem ggQ2xA3c_simpleRefl_inv (D : GGQ2Lin 3) (k : D.ι) :
    (D.simpleRefl k)⁻¹ = D.simpleRefl k := by
  rw [GGQ2Lin.simpleRefl, Module.reflection_inv]

private theorem ggQ2xA3c_gen (D : GGQ2Lin 3) (f : Fin 3 ≃ {k // k ≠ D.a})
    (hf : ∀ i j, (D.cartan (f i).1 (f j).1 : ZMod 3) = ggQ2xA3_C i j) (i : Fin 3) :
    ggQ2xA3c_Pform D f (D.simpleRefl (f i).1) (ggQ2xA3_S i) := by
  intro v
  rw [GGQ2Lin.simpleRefl, Module.reflection_apply, sub_eq_add_neg]
  congr 1
  have h1 : (ggQ2xA3_S i - 1).mulVec (ggQ2xA3c_pi D f v)
      = -(((ggQ2xA3_C.mulVec (ggQ2xA3c_pi D f v)) i) • Pi.single i 1) := by
    rw [ggQ2xA3_S, Matrix.sub_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec,
      ← Matrix.mulVec_mulVec, Matrix.single_mulVec_eq, one_mul]
    abel
  rw [h1, map_neg, ggQ2xA3c_Qv_single, ggQ2xA3c_C_mulVec_pi]

private theorem ggQ2xA3c_Pform_one (D : GGQ2Lin 3) (f : Fin 3 ≃ {k // k ≠ D.a}) :
    ggQ2xA3c_Pform D f 1 1 := by
  intro v
  simp [ggQ2xA3c_Pform]

private theorem ggQ2xA3c_pi_Pform (D : GGQ2Lin 3) (f : Fin 3 ≃ {k // k ≠ D.a})
    (hf : ∀ i j, (D.cartan (f i).1 (f j).1 : ZMod 3) = ggQ2xA3_C i j)
    {g : D.V ≃ₗ[ZMod 3] D.V} {N : Matrix (Fin 3) (Fin 3) (ZMod 3)}
    (h : ggQ2xA3c_Pform D f g N) (v : D.V) :
    ggQ2xA3c_pi D f (g v) = N.mulVec (ggQ2xA3c_pi D f v) := by
  calc ggQ2xA3c_pi D f (g v)
      = ggQ2xA3c_pi D f
          (v + ggQ2xA3c_Qv D f ((N - 1).mulVec (ggQ2xA3c_pi D f v))) := by rw [h v]
    _ = ggQ2xA3c_pi D f v + (N - 1).mulVec (ggQ2xA3c_pi D f v) := by
        rw [map_add, ggQ2xA3c_pi_Qv D f hf]
    _ = Matrix.mulVec 1 (ggQ2xA3c_pi D f v) + Matrix.mulVec (N - 1) (ggQ2xA3c_pi D f v) := by
        rw [Matrix.one_mulVec]
    _ = Matrix.mulVec (1 + (N - 1)) (ggQ2xA3c_pi D f v) := by rw [Matrix.add_mulVec]
    _ = N.mulVec (ggQ2xA3c_pi D f v) := by rw [add_sub_cancel]

private theorem ggQ2xA3c_Pform_mul (D : GGQ2Lin 3) (f : Fin 3 ≃ {k // k ≠ D.a})
    (hf : ∀ i j, (D.cartan (f i).1 (f j).1 : ZMod 3) = ggQ2xA3_C i j)
    {g h : D.V ≃ₗ[ZMod 3] D.V} {N N' : Matrix (Fin 3) (Fin 3) (ZMod 3)}
    (hg : ggQ2xA3c_Pform D f g N) (hh : ggQ2xA3c_Pform D f h N') :
    ggQ2xA3c_Pform D f (g * h) (N * N') := by
  intro v
  calc (g * h) v
      = g (h v) := rfl
    _ = h v + ggQ2xA3c_Qv D f ((N - 1).mulVec (ggQ2xA3c_pi D f (h v))) := by rw [hg]
    _ = h v + ggQ2xA3c_Qv D f ((N - 1).mulVec (Matrix.mulVec N' (ggQ2xA3c_pi D f v))) := by
        rw [ggQ2xA3c_pi_Pform D f hf hh v]
    _ = (v + ggQ2xA3c_Qv D f ((N' - 1).mulVec (ggQ2xA3c_pi D f v)))
          + ggQ2xA3c_Qv D f ((N - 1).mulVec (Matrix.mulVec N' (ggQ2xA3c_pi D f v))) := by
        rw [hh v]
    _ = v + ggQ2xA3c_Qv D f (((N * N') - 1).mulVec (ggQ2xA3c_pi D f v)) := by
        rw [add_assoc, ← map_add]
        congr 1
        rw [Matrix.mulVec_mulVec, ← Matrix.add_mulVec]
        congr 1
        rw [Matrix.sub_mul, Matrix.one_mul]
        abel_nf

private theorem ggQ2xA3c_forward (D : GGQ2Lin 3) (f : Fin 3 ≃ {k // k ≠ D.a})
    (hf : ∀ i j, (D.cartan (f i).1 (f j).1 : ZMod 3) = ggQ2xA3_C i j) :
    ∀ g ∈ D.parab {k | k ≠ D.a}, ∃ N ∈ Submonoid.closure (Set.range ggQ2xA3_S),
      ggQ2xA3c_Pform D f g N := by
  let M := Submonoid.closure (Set.range ggQ2xA3_S)
  let Sset : Set D.ι := {k | k ≠ D.a}
  have key : ∀ g ∈ D.parab Sset,
      (∃ N ∈ M, ggQ2xA3c_Pform D f g N) ∧
      (∃ N ∈ M, ggQ2xA3c_Pform D f g⁻¹ N) := by
    intro g hg
    let p : (x : D.V ≃ₗ[ZMod 3] D.V) →
        x ∈ Subgroup.closure (D.simpleRefl '' Sset) → Prop :=
      fun x _ => (∃ N ∈ M, ggQ2xA3c_Pform D f x N) ∧
        (∃ N ∈ M, ggQ2xA3c_Pform D f x⁻¹ N)
    have hg' : g ∈ Subgroup.closure (D.simpleRefl '' Sset) := hg
    change p g hg'
    refine Subgroup.closure_induction (p := p) (k := D.simpleRefl '' Sset) ?_ ?_ ?_ ?_ hg'
    · intro x hx
      obtain ⟨k, hk, hkx⟩ := hx
      set i : Fin 3 := f.symm ⟨k, hk⟩ with hi
      have hfi : (f i).1 = k := by simp [hi]
      have hgen := ggQ2xA3c_gen D f hf i
      constructor
      · refine ⟨ggQ2xA3_S i, Submonoid.subset_closure ⟨i, rfl⟩, ?_⟩
        rw [← hkx, ← hfi]
        exact hgen
      · refine ⟨ggQ2xA3_S i, Submonoid.subset_closure ⟨i, rfl⟩, ?_⟩
        rw [← hkx, ← hfi, ggQ2xA3c_simpleRefl_inv]
        exact hgen
    · exact ⟨⟨1, M.one_mem, ggQ2xA3c_Pform_one D f⟩,
             ⟨1, M.one_mem, by rw [inv_one]; exact ggQ2xA3c_Pform_one D f⟩⟩
    · intro x y hx hy px py
      obtain ⟨⟨Nx, hNxM, hNx⟩, Nxi, hNxiM, hNxi⟩ := px
      obtain ⟨⟨Ny, hNyM, hNy⟩, Nyi, hNyiM, hNyi⟩ := py
      exact ⟨⟨Nx * Ny, M.mul_mem hNxM hNyM,
                ggQ2xA3c_Pform_mul D f hf hNx hNy⟩,
             ⟨Nyi * Nxi, M.mul_mem hNyiM hNxiM, by
                rw [_root_.mul_inv_rev]
                exact ggQ2xA3c_Pform_mul D f hf hNyi hNxi⟩⟩
    · intro x hx px
      exact ⟨px.2, by rw [inv_inv]; exact px.1⟩
  intro g hg
  exact (key g hg).1

private theorem ggQ2xA3c_backward (D : GGQ2Lin 3) (f : Fin 3 ≃ {k // k ≠ D.a})
    (hf : ∀ i j, (D.cartan (f i).1 (f j).1 : ZMod 3) = ggQ2xA3_C i j) :
    ∀ N ∈ Submonoid.closure (Set.range ggQ2xA3_S),
      ∃ g ∈ D.parab {k | k ≠ D.a}, ggQ2xA3c_Pform D f g N := by
  let Sset : Set D.ι := {k | k ≠ D.a}
  let M' : Submonoid (Matrix (Fin 3) (Fin 3) (ZMod 3)) :=
    { carrier := {N | ∃ g ∈ D.parab Sset, ggQ2xA3c_Pform D f g N}
      one_mem' := ⟨1, (D.parab Sset).one_mem, ggQ2xA3c_Pform_one D f⟩
      mul_mem' := by
        rintro a b ⟨g, hg, hga⟩ ⟨h, hh, hhb⟩
        refine ⟨g * h, (D.parab Sset).mul_mem hg hh, ?_⟩
        exact ggQ2xA3c_Pform_mul D f hf hga hhb }
  intro N hN
  exact (Submonoid.closure_le (s := Set.range ggQ2xA3_S) (S := M')).2 (by
    rintro N ⟨i, rfl⟩
    exact ⟨D.simpleRefl (f i).1, Subgroup.mem_closure_of_mem ⟨(f i).1, (f i).2, rfl⟩,
      ggQ2xA3c_gen D f hf i⟩) hN

private theorem ggQ2xA3c_Pform_Qv (D : GGQ2Lin 3) (f : Fin 3 ≃ {k // k ≠ D.a})
    (hf : ∀ i j, (D.cartan (f i).1 (f j).1 : ZMod 3) = ggQ2xA3_C i j)
    {g : D.V ≃ₗ[ZMod 3] D.V} {N : Matrix (Fin 3) (Fin 3) (ZMod 3)}
    (h : ggQ2xA3c_Pform D f g N) (c : Fin 3 → ZMod 3) :
    g (ggQ2xA3c_Qv D f c) = ggQ2xA3c_Qv D f (N.mulVec c) := by
  calc g (ggQ2xA3c_Qv D f c)
      = ggQ2xA3c_Qv D f c
          + ggQ2xA3c_Qv D f ((N - 1).mulVec
              (ggQ2xA3c_pi D f (ggQ2xA3c_Qv D f c))) := by rw [h]
    _ = ggQ2xA3c_Qv D f (Matrix.mulVec 1 c) + ggQ2xA3c_Qv D f (Matrix.mulVec (N - 1) c) := by
        rw [ggQ2xA3c_pi_Qv D f hf c, Matrix.one_mulVec]
    _ = ggQ2xA3c_Qv D f (Matrix.mulVec 1 c + Matrix.mulVec (N - 1) c) := by rw [map_add]
    _ = ggQ2xA3c_Qv D f (Matrix.mulVec (1 + (N - 1)) c) := by rw [Matrix.add_mulVec]
    _ = ggQ2xA3c_Qv D f (N.mulVec c) := by rw [add_sub_cancel]

private theorem ggQ2xA3c_Pform_unique (D : GGQ2Lin 3) (f : Fin 3 ≃ {k // k ≠ D.a})
    (hf : ∀ i j, (D.cartan (f i).1 (f j).1 : ZMod 3) = ggQ2xA3_C i j)
    {g : D.V ≃ₗ[ZMod 3] D.V} {N N' : Matrix (Fin 3) (Fin 3) (ZMod 3)}
    (hN : ggQ2xA3c_Pform D f g N) (hN' : ggQ2xA3c_Pform D f g N') : N = N' := by
  have h : ∀ c : Fin 3 → ZMod 3, N.mulVec c = N'.mulVec c := by
    intro c
    apply ggQ2xA3c_Qv_injective D f hf
    rw [← ggQ2xA3c_Pform_Qv D f hf hN c, ← ggQ2xA3c_Pform_Qv D f hf hN' c]
  ext i j
  have hij := congrFun (h (Pi.single j 1)) i
  simpa [Matrix.mulVec_single_one] using hij

private theorem ggQ2xA3_card_of_cartan (D : GGQ2Lin 3) (f : Fin 3 ≃ {k // k ≠ D.a})
    (hf : ∀ i j, (D.cartan (f i).1 (f j).1 : ZMod 3) = ggQ2xA3_C i j) :
    Nat.card (D.parab {k | k ≠ D.a}) = 24 := by
  let M := Submonoid.closure (Set.range ggQ2xA3_S)
  let Sset : Set D.ι := {k | k ≠ D.a}
  have fwd := ggQ2xA3c_forward D f hf
  have bwd := ggQ2xA3c_backward D f hf
  let ρ : D.parab Sset → M := fun g =>
    ⟨Classical.choose (fwd g g.2), (Classical.choose_spec (fwd g g.2)).1⟩
  have hρspec : ∀ g : D.parab Sset, ggQ2xA3c_Pform D f g.1 (ρ g).1 := fun g =>
    (Classical.choose_spec (fwd g g.2)).2
  have hinj : Function.Injective ρ := by
    intro g g' h
    apply Subtype.ext
    apply LinearEquiv.ext
    intro v
    have hN : (ρ g).1 = (ρ g').1 := congrArg Subtype.val h
    rw [hρspec g v, hρspec g' v, hN]
  have hsurj : Function.Surjective ρ := by
    intro N
    obtain ⟨g, hg, hgN⟩ := bwd N.1 N.2
    refine ⟨⟨g, hg⟩, ?_⟩
    apply Subtype.ext
    exact ggQ2xA3c_Pform_unique D f hf (hρspec ⟨g, hg⟩) hgN
  have hcard := Nat.card_congr (Equiv.ofBijective ρ ⟨hinj, hsurj⟩)
  change Nat.card (D.parab Sset) = 24
  rw [hcard]
  exact ggQ2xA3_card

theorem ggQ2_parab_card_A3 (D : GGQ2Lin 3) (e : Fin 4 ≃ D.ι)
    (h : (D.coxeter = (CoxeterMatrix.A 4).reindex e ∧ (D.a = e 0 ∨ D.a = e 3)) ∨
      (D.coxeter = (ggCoxeterMatrixD 4).reindex e ∧ (D.a = e 0 ∨ D.a = e 2 ∨ D.a = e 3)) ∨
      (D.coxeter = (CoxeterMatrix.B 4).reindex e ∧ D.a = e 3)) :
    Nat.card (D.parab {k | k ≠ D.a}) = 24 := by
  obtain ⟨f, hf⟩ := ggQ2xA3_cartan D e h
  exact ggQ2xA3_card_of_cartan D f hf

end CFSG.StandardType

end
