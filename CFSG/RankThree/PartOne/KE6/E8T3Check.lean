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

set_option maxRecDepth 100000 in
theorem e8T3_candidates : ∀ J : Finset (Fin Tag.E8.rank), J ≠ Finset.univ →
    J.card % 2 = 0 → 3 ∣ e8PhiCard J → J ∈ e8T3Supports ∨ J ∈ e8T3Excluded := by
  decide +kernel

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
