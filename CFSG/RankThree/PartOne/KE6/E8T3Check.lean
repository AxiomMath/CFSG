module

public import CFSG.RankThree.PartOne.KE6.E8T3Engine

public noncomputable section

namespace CFSG.RankThree.PartOne.KE6

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.E6 CFSG.RankThree.Lattice
  CFSG.LieType.Steinberg.Adjoint

@[expose] def e8T3Supports : List (Finset (Fin Tag.E8.rank)) :=
  [∅, {0, 2}, {1, 3}, {2, 3}, {3, 4}, {4, 5}, {5, 6}, {6, 7},
   {0, 2, 4, 5}, {0, 2, 5, 6}, {0, 2, 6, 7}, {1, 3, 5, 6}, {1, 3, 6, 7}, {2, 3, 5, 6},
   {2, 3, 6, 7}, {3, 4, 6, 7}, {1, 2, 3, 4}, {0, 1, 2, 3, 4, 5}, {1, 2, 3, 4, 6, 7}]

@[expose] def e8PhiCard (J : Finset (Fin Tag.E8.rank)) : ℕ :=
  (Tag.E8.artifactRoots.filter fun l => decide (∀ i, i ∉ J → toVec Tag.E8.rank l i = 0)).length

@[expose] def e8T3Excluded : List (Finset (Fin Tag.E8.rank)) :=
  [{0, 1, 2, 3, 4, 6}, {0, 1, 2, 3, 4, 7}, {0, 1, 2, 3, 5, 7}, {0, 1, 3, 4, 5, 7},
   {0, 1, 4, 5, 6, 7}, {0, 2, 3, 4, 5, 6}, {0, 2, 3, 5, 6, 7}, {1, 2, 3, 4, 5, 6},
   {1, 2, 3, 4, 5, 7}, {1, 2, 3, 5, 6, 7}, {1, 2, 4, 5, 6, 7}, {1, 3, 4, 5, 6, 7},
   {2, 3, 4, 5, 6, 7}]

@[expose] def e8SuppL (l : List ℤ) : List (Fin Tag.E8.rank) :=
  (List.finRange Tag.E8.rank).filter fun i => decide (toVec Tag.E8.rank l i ≠ 0)

@[expose] def e8SuppLs : List (List (Fin Tag.E8.rank)) := [
    [0, 1, 2, 3, 4, 5, 6, 7], [0, 1, 2, 3, 4, 5, 6, 7], [0, 1, 2, 3, 4, 5, 6, 7],
    [0, 1, 2, 3, 4, 5, 6, 7], [0, 1, 2, 3, 4, 5, 6, 7], [0, 1, 2, 3, 4, 5, 6, 7],
    [0, 1, 2, 3, 4, 5, 6, 7], [0, 1, 2, 3, 4, 5, 6, 7], [0, 1, 2, 3, 4, 5, 6, 7],
    [0, 1, 2, 3, 4, 5, 6, 7], [0, 1, 2, 3, 4, 5, 6, 7], [0, 1, 2, 3, 4, 5, 6, 7],
    [0, 1, 2, 3, 4, 5, 6, 7], [0, 1, 2, 3, 4, 5, 6], [0, 1, 2, 3, 4, 5, 6, 7],
    [0, 1, 2, 3, 4, 5, 6, 7], [0, 1, 2, 3, 4, 5, 6, 7], [0, 1, 2, 3, 4, 5, 6, 7],
    [0, 1, 2, 3, 4, 5, 6, 7], [0, 1, 2, 3, 4, 5, 6, 7], [0, 1, 2, 3, 4, 5, 6],
    [0, 1, 2, 3, 4, 5, 6, 7], [0, 1, 2, 3, 4, 5, 6, 7], [0, 1, 2, 3, 4, 5, 6, 7],
    [0, 1, 2, 3, 4, 5, 6, 7], [0, 1, 2, 3, 4, 5, 6], [0, 1, 2, 3, 4, 5, 6, 7],
    [0, 1, 2, 3, 4, 5, 6, 7], [0, 1, 2, 3, 4, 5, 6, 7], [0, 1, 2, 3, 4, 5, 6],
    [0, 1, 2, 3, 4, 5, 6, 7], [0, 1, 2, 3, 4, 5, 6, 7], [0, 1, 2, 3, 4, 5, 6],
    [0, 1, 2, 3, 4, 5, 6, 7], [0, 1, 2, 3, 4, 5, 6], [0, 1, 2, 3, 4, 5], [0, 1, 2, 3, 4, 5, 6, 7],
    [0, 1, 2, 3, 4, 5, 6, 7], [0, 1, 2, 3, 4, 5, 6, 7], [0, 1, 2, 3, 4, 5, 6],
    [0, 1, 2, 3, 4, 5, 6, 7], [0, 1, 2, 3, 4, 5, 6, 7], [0, 1, 2, 3, 4, 5, 6],
    [0, 1, 2, 3, 4, 5, 6, 7], [0, 1, 2, 3, 4, 5, 6], [0, 1, 2, 3, 4, 5], [0, 1, 2, 3, 4, 5, 6, 7],
    [0, 1, 2, 3, 4, 5, 6, 7], [0, 1, 2, 3, 4, 5, 6], [0, 1, 2, 3, 4, 5, 6, 7],
    [0, 1, 2, 3, 4, 5, 6], [0, 1, 2, 3, 4, 5], [0, 1, 2, 3, 4, 5, 6, 7], [0, 1, 2, 3, 4, 5, 6],
    [0, 1, 2, 3, 4, 5], [0, 1, 2, 3, 4], [0, 1, 2, 3, 4, 5, 6, 7], [0, 1, 2, 3, 4, 5, 6, 7],
    [0, 1, 2, 3, 4, 5, 6], [0, 1, 2, 3, 4, 5, 6, 7], [0, 1, 2, 3, 4, 5, 6], [0, 1, 2, 3, 4, 5],
    [0, 1, 2, 3, 4, 5, 6, 7], [0, 1, 2, 3, 4, 5, 6], [0, 1, 2, 3, 4, 5], [0, 1, 2, 3, 4],
    [0, 1, 2, 3, 4, 5, 6, 7], [0, 1, 2, 3, 4, 5, 6], [0, 1, 2, 3, 4, 5], [0, 1, 2, 3, 4],
    [0, 1, 2, 3], [0, 2, 3, 4, 5, 6, 7], [0, 2, 3, 4, 5, 6], [0, 2, 3, 4, 5], [0, 2, 3, 4],
    [0, 2, 3], [0, 2], [0], [1, 2, 3, 4, 5, 6, 7], [1, 2, 3, 4, 5, 6, 7], [1, 2, 3, 4, 5, 6],
    [1, 2, 3, 4, 5, 6, 7], [1, 2, 3, 4, 5, 6], [1, 2, 3, 4, 5], [1, 2, 3, 4, 5, 6, 7],
    [1, 2, 3, 4, 5, 6], [1, 2, 3, 4, 5], [1, 2, 3, 4], [1, 2, 3, 4, 5, 6, 7], [1, 2, 3, 4, 5, 6],
    [1, 2, 3, 4, 5], [1, 2, 3, 4], [1, 2, 3], [1, 3, 4, 5, 6, 7], [1, 3, 4, 5, 6], [1, 3, 4, 5],
    [1, 3, 4], [1, 3], [1], [2, 3, 4, 5, 6, 7], [2, 3, 4, 5, 6], [2, 3, 4, 5], [2, 3, 4], [2, 3],
    [2], [3, 4, 5, 6, 7], [3, 4, 5, 6], [3, 4, 5], [3, 4], [3], [4, 5, 6, 7], [4, 5, 6], [4, 5],
    [4], [5, 6, 7], [5, 6], [5], [6, 7], [6], [7], [7], [6], [6, 7], [5], [5, 6], [5, 6, 7], [4],
    [4, 5], [4, 5, 6], [4, 5, 6, 7], [3], [3, 4], [3, 4, 5], [3, 4, 5, 6], [3, 4, 5, 6, 7], [2],
    [2, 3], [2, 3, 4], [2, 3, 4, 5], [2, 3, 4, 5, 6], [2, 3, 4, 5, 6, 7], [1], [1, 3], [1, 3, 4],
    [1, 3, 4, 5], [1, 3, 4, 5, 6], [1, 3, 4, 5, 6, 7], [1, 2, 3], [1, 2, 3, 4], [1, 2, 3, 4, 5],
    [1, 2, 3, 4, 5, 6], [1, 2, 3, 4, 5, 6, 7], [1, 2, 3, 4], [1, 2, 3, 4, 5], [1, 2, 3, 4, 5, 6],
    [1, 2, 3, 4, 5, 6, 7], [1, 2, 3, 4, 5], [1, 2, 3, 4, 5, 6], [1, 2, 3, 4, 5, 6, 7],
    [1, 2, 3, 4, 5, 6], [1, 2, 3, 4, 5, 6, 7], [1, 2, 3, 4, 5, 6, 7], [0], [0, 2], [0, 2, 3],
    [0, 2, 3, 4], [0, 2, 3, 4, 5], [0, 2, 3, 4, 5, 6], [0, 2, 3, 4, 5, 6, 7], [0, 1, 2, 3],
    [0, 1, 2, 3, 4], [0, 1, 2, 3, 4, 5], [0, 1, 2, 3, 4, 5, 6], [0, 1, 2, 3, 4, 5, 6, 7],
    [0, 1, 2, 3, 4], [0, 1, 2, 3, 4, 5], [0, 1, 2, 3, 4, 5, 6], [0, 1, 2, 3, 4, 5, 6, 7],
    [0, 1, 2, 3, 4, 5], [0, 1, 2, 3, 4, 5, 6], [0, 1, 2, 3, 4, 5, 6, 7], [0, 1, 2, 3, 4, 5, 6],
    [0, 1, 2, 3, 4, 5, 6, 7], [0, 1, 2, 3, 4, 5, 6, 7], [0, 1, 2, 3, 4], [0, 1, 2, 3, 4, 5],
    [0, 1, 2, 3, 4, 5, 6], [0, 1, 2, 3, 4, 5, 6, 7], [0, 1, 2, 3, 4, 5], [0, 1, 2, 3, 4, 5, 6],
    [0, 1, 2, 3, 4, 5, 6, 7], [0, 1, 2, 3, 4, 5, 6], [0, 1, 2, 3, 4, 5, 6, 7],
    [0, 1, 2, 3, 4, 5, 6, 7], [0, 1, 2, 3, 4, 5], [0, 1, 2, 3, 4, 5, 6], [0, 1, 2, 3, 4, 5, 6, 7],
    [0, 1, 2, 3, 4, 5, 6], [0, 1, 2, 3, 4, 5, 6, 7], [0, 1, 2, 3, 4, 5, 6, 7],
    [0, 1, 2, 3, 4, 5, 6], [0, 1, 2, 3, 4, 5, 6, 7], [0, 1, 2, 3, 4, 5, 6, 7],
    [0, 1, 2, 3, 4, 5, 6, 7], [0, 1, 2, 3, 4, 5], [0, 1, 2, 3, 4, 5, 6], [0, 1, 2, 3, 4, 5, 6, 7],
    [0, 1, 2, 3, 4, 5, 6], [0, 1, 2, 3, 4, 5, 6, 7], [0, 1, 2, 3, 4, 5, 6, 7],
    [0, 1, 2, 3, 4, 5, 6], [0, 1, 2, 3, 4, 5, 6, 7], [0, 1, 2, 3, 4, 5, 6, 7],
    [0, 1, 2, 3, 4, 5, 6, 7], [0, 1, 2, 3, 4, 5, 6], [0, 1, 2, 3, 4, 5, 6, 7],
    [0, 1, 2, 3, 4, 5, 6, 7], [0, 1, 2, 3, 4, 5, 6, 7], [0, 1, 2, 3, 4, 5, 6, 7],
    [0, 1, 2, 3, 4, 5, 6], [0, 1, 2, 3, 4, 5, 6, 7], [0, 1, 2, 3, 4, 5, 6, 7],
    [0, 1, 2, 3, 4, 5, 6, 7], [0, 1, 2, 3, 4, 5, 6, 7], [0, 1, 2, 3, 4, 5, 6, 7],
    [0, 1, 2, 3, 4, 5, 6, 7], [0, 1, 2, 3, 4, 5, 6], [0, 1, 2, 3, 4, 5, 6, 7],
    [0, 1, 2, 3, 4, 5, 6, 7], [0, 1, 2, 3, 4, 5, 6, 7], [0, 1, 2, 3, 4, 5, 6, 7],
    [0, 1, 2, 3, 4, 5, 6, 7], [0, 1, 2, 3, 4, 5, 6, 7], [0, 1, 2, 3, 4, 5, 6, 7],
    [0, 1, 2, 3, 4, 5, 6, 7], [0, 1, 2, 3, 4, 5, 6, 7], [0, 1, 2, 3, 4, 5, 6, 7],
    [0, 1, 2, 3, 4, 5, 6, 7], [0, 1, 2, 3, 4, 5, 6, 7], [0, 1, 2, 3, 4, 5, 6, 7]]

theorem e8SuppLs_eq : Tag.E8.artifactRoots.map e8SuppL = e8SuppLs := by
  decide +kernel

theorem e8SuppL_all_iff (J : Finset (Fin Tag.E8.rank)) (l : List ℤ) :
    (∀ i, i ∉ J → toVec Tag.E8.rank l i = 0) ↔ ((e8SuppL l).all fun i => decide (i ∈ J)) = true := by
  rw [List.all_eq_true]
  constructor
  · intro h i hi
    rw [e8SuppL, List.mem_filter, decide_eq_true_iff] at hi
    rw [decide_eq_true_iff]
    by_contra hJ
    exact hi.2 (h i hJ)
  · intro h i hi
    by_contra hne
    have := h i (List.mem_filter.2 ⟨List.mem_finRange i, (decide_eq_true_iff).2 hne⟩)
    exact hi ((decide_eq_true_iff).1 this)

theorem e8PhiCard_eq (J : Finset (Fin Tag.E8.rank)) :
    e8PhiCard J = (e8SuppLs.filter fun s => s.all fun i => decide (i ∈ J)).length := by
  unfold e8PhiCard
  rw [← e8SuppLs_eq, List.filter_map, List.length_map]
  congr 1
  apply List.filter_congr
  intro l _
  rw [Bool.eq_iff_iff, decide_eq_true_iff]
  exact e8SuppL_all_iff J l

set_option maxRecDepth 100000 in
theorem e8T3_candidates_check : ∀ J : Finset (Fin Tag.E8.rank), J ≠ Finset.univ →
    J.card % 2 = 0 → 3 ∣ (e8SuppLs.filter fun s => s.all fun i => decide (i ∈ J)).length →
      J ∈ e8T3Supports ∨ J ∈ e8T3Excluded := by
  decide +kernel

theorem e8T3_candidates : ∀ J : Finset (Fin Tag.E8.rank), J ≠ Finset.univ →
    J.card % 2 = 0 → 3 ∣ e8PhiCard J → J ∈ e8T3Supports ∨ J ∈ e8T3Excluded :=
  fun J h1 h2 h3 => e8T3_candidates_check J h1 h2 (by rwa [e8PhiCard_eq] at h3)

set_option maxRecDepth 100000 in
theorem e8T3_noT_1 : noT (jlist ({0, 1, 2, 3, 4, 6} : Finset (Fin Tag.E8.rank))) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem e8T3_noT_2 : noT (jlist ({0, 1, 2, 3, 4, 7} : Finset (Fin Tag.E8.rank))) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem e8T3_noT_3 : noT (jlist ({0, 1, 2, 3, 5, 7} : Finset (Fin Tag.E8.rank))) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem e8T3_noT_4 : noT (jlist ({0, 1, 3, 4, 5, 7} : Finset (Fin Tag.E8.rank))) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem e8T3_noT_5 : noT (jlist ({0, 1, 4, 5, 6, 7} : Finset (Fin Tag.E8.rank))) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem e8T3_noT_6 : noT (jlist ({0, 2, 3, 4, 5, 6} : Finset (Fin Tag.E8.rank))) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem e8T3_noT_7 : noT (jlist ({0, 2, 3, 5, 6, 7} : Finset (Fin Tag.E8.rank))) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem e8T3_noT_8 : noT (jlist ({1, 2, 3, 4, 5, 6} : Finset (Fin Tag.E8.rank))) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem e8T3_noT_9 : noT (jlist ({1, 2, 3, 4, 5, 7} : Finset (Fin Tag.E8.rank))) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem e8T3_noT_10 : noT (jlist ({1, 2, 3, 5, 6, 7} : Finset (Fin Tag.E8.rank))) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem e8T3_noT_11 : noT (jlist ({1, 2, 4, 5, 6, 7} : Finset (Fin Tag.E8.rank))) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem e8T3_noT_12 : noT (jlist ({1, 3, 4, 5, 6, 7} : Finset (Fin Tag.E8.rank))) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem e8T3_noT_13 : noT (jlist ({2, 3, 4, 5, 6, 7} : Finset (Fin Tag.E8.rank))) = true := by
  decide +kernel

theorem e8T3_excluded_noT : ∀ J ∈ e8T3Excluded, noT (jlist J) = true := by
  intro J hJ
  simp only [e8T3Excluded, List.mem_cons, List.not_mem_nil, or_false] at hJ
  rcases hJ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [e8T3_noT_1, e8T3_noT_2, e8T3_noT_3, e8T3_noT_4, e8T3_noT_5, e8T3_noT_6, e8T3_noT_7,
    e8T3_noT_8, e8T3_noT_9, e8T3_noT_10, e8T3_noT_11, e8T3_noT_12, e8T3_noT_13]

theorem e8T3_finite_check : ∀ J : Finset (Fin Tag.E8.rank), J ≠ Finset.univ →
    J.card % 2 = 0 → 3 ∣ e8PhiCard J → J ∈ e8T3Supports ∨ noT (jlist J) = true := fun J h1 h2 h3 =>
  (e8T3_candidates J h1 h2 h3).imp id (e8T3_excluded_noT J)

end CFSG.RankThree.PartOne.KE6
