module

public import CFSG.RankThree.PartOne.SEITZ4.SpGen

public section

namespace CFSG.RankThree.PartOne.SEITZ4

open Matrix CFSG.Assembly.LowTwoRank CFSG.RankThree.SubgroupLists

variable {r : ℕ} {K : Type} [Field K] [CharP K 2]

theorem spForm_single_single (a b : Fin r ⊕ Fin r) :
    spForm r K (Pi.single a (1 : K)) (Pi.single b 1) = if a = b.swap then 1 else 0 := by
  rw [spForm_single_right]
  by_cases h : a = b.swap
  · simp [h]
  · simp [Ne.symm h, h]

theorem spForm_comm_single (u : Fin r ⊕ Fin r → K) (a : Fin r ⊕ Fin r) :
    spForm r K (Pi.single a 1) u = u a.swap := by
  rw [spForm_comm', spForm_single_right]

theorem pair_of_ne_swap (k : Subfield K) {u : Fin r ⊕ Fin r → K} {i j : Fin r ⊕ Fin r}
    (hi : u i ≠ 0) (hj : u j ≠ 0) (hji : u j ≠ u i) (hs : j ≠ i.swap) :
    ∃ e w : Fin r ⊕ Fin r → K, IsRat k e ∧ IsRat k w ∧ spForm r K e w = 0 ∧
      spForm r K e u ≠ 0 ∧ spForm r K w u ≠ 0 ∧ spForm r K w u ≠ spForm r K e u := by
  refine ⟨Pi.single i.swap 1, Pi.single j.swap 1, isRat_single k _, isRat_single k _, ?_, ?_,
    ?_, ?_⟩
  · rw [spForm_single_single, Sum.swap_swap]
    simp [Ne.symm hs]
  · rw [spForm_comm_single, Sum.swap_swap]
    exact hi
  · rw [spForm_comm_single, Sum.swap_swap]
    exact hj
  · rw [spForm_comm_single, spForm_comm_single, Sum.swap_swap, Sum.swap_swap]
    exact hji

theorem exists_index_ne (hr : 2 ≤ r) (i : Fin r ⊕ Fin r) :
    ∃ l : Fin r ⊕ Fin r, l ≠ i ∧ l ≠ i.swap := by
  have h1 : 1 < Fintype.card (Fin r) := by rw [Fintype.card_fin]; omega
  rcases i with a | a
  · obtain ⟨c, hc⟩ := Fintype.exists_ne_of_one_lt_card h1 a
    exact ⟨Sum.inl c, by simpa using hc, by simp⟩
  · obtain ⟨c, hc⟩ := Fintype.exists_ne_of_one_lt_card h1 a
    exact ⟨Sum.inl c, by simp, by simpa using hc⟩

theorem exists_orthogonal_pair (k : Subfield K) (hr : 2 ≤ r) {u : Fin r ⊕ Fin r → K}
    {i j : Fin r ⊕ Fin r} (hi : u i ≠ 0) (hj : u j ≠ 0) (hji : u j ≠ u i) :
    ∃ e w : Fin r ⊕ Fin r → K, IsRat k e ∧ IsRat k w ∧ spForm r K e w = 0 ∧
      spForm r K e u ≠ 0 ∧ spForm r K w u ≠ 0 ∧ spForm r K w u ≠ spForm r K e u := by
  by_cases hs : j = i.swap
  · obtain ⟨l, hl1, hl2⟩ := exists_index_ne hr i
    by_cases hz : ∃ l' : Fin r ⊕ Fin r, l' ≠ i ∧ l' ≠ i.swap ∧ u l' ≠ 0
    · obtain ⟨l', hl1', hl2', hl0⟩ := hz
      by_cases hli : u l' = u i
      · refine pair_of_ne_swap k hj hl0 ?_ ?_
        · rw [hli]
          exact fun h => hji h.symm
        · rw [hs, Sum.swap_swap]
          exact hl1'
      · exact pair_of_ne_swap k hi hl0 hli hl2'
    · push Not at hz
      have hl0 : u l = 0 := hz l hl1 hl2
      have hl0' : u l.swap = 0 := by
        refine hz l.swap ?_ ?_
        · intro h
          exact hl2 (by rw [← h, Sum.swap_swap])
        · intro h
          exact hl1 (by rw [← Sum.swap_swap l, h, Sum.swap_swap])
      refine ⟨Pi.single i.swap 1 + Pi.single l 1, Pi.single i 1 + Pi.single l.swap 1,
        isRat_add (isRat_single k _) (isRat_single k _),
        isRat_add (isRat_single k _) (isRat_single k _), ?_, ?_, ?_, ?_⟩
      · simp only [map_add, LinearMap.add_apply, spForm_single_single, Sum.swap_swap]
        have h1 : (i.swap = i.swap) = True := eq_self _
        have h2 : ¬ i.swap = l := fun h => hl2 h.symm
        have h3 : ¬ l = i.swap := hl2
        simp [h2, h3]
        exact CharTwo.add_self_eq_zero _
      · simp only [map_add, LinearMap.add_apply, spForm_comm_single, Sum.swap_swap, hl0']
        simpa using hi
      · simp only [map_add, LinearMap.add_apply, spForm_comm_single, Sum.swap_swap, hl0]
        rw [← hs]
        simpa using hj
      · simp only [map_add, LinearMap.add_apply, spForm_comm_single, Sum.swap_swap, hl0, hl0']
        rw [← hs]
        simpa using hji
  · exact pair_of_ne_swap k hi hj hji hs

end CFSG.RankThree.PartOne.SEITZ4
