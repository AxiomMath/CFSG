module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S21a

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G] {M L : Subgroup G}

theorem ncard_conjSetOf_le_two_of_three_conj_rank
    (hthree : ∀ L₁ ∈ conjSetOf M L, ∀ L₂ ∈ conjSetOf M L, ∀ L₃ ∈ conjSetOf M L,
      L₁ ≠ L₂ → L₁ ≠ L₃ → L₂ ≠ L₃ → 4 ≤ CFSG.Open.pRank 3 M)
    (hbound : CFSG.Open.pRank 3 M ≤ 3) :
    (conjSetOf M L).ncard ≤ 2 := by
  classical
  by_contra h
  have h3 : 3 ≤ (conjSetOf M L).ncard := by omega
  obtain ⟨t, ht_sub, ht_card⟩ :=
    Set.exists_subset_card_eq (s := conjSetOf M L) (n := 3) h3
  obtain ⟨L₁, L₂, L₃, h12, h13, h23, rfl⟩ := Set.ncard_eq_three.mp ht_card
  have h4 := hthree L₁ (ht_sub (by simp)) L₂ (ht_sub (by simp)) L₃ (ht_sub (by simp))
    h12 h13 h23
  omega

theorem exists_pair_eq_conjSetOf_of_ncard_eq_two (hL : L ∈ conjSetOf M L)
    (h : (conjSetOf M L).ncard = 2) :
    ∃ L' : Subgroup G, L' ≠ L ∧ conjSetOf M L = {L, L'} := by
  obtain ⟨A, B, hAB, hset⟩ := Set.ncard_eq_two.mp h
  have hL' : L = A ∨ L = B := by
    have : L ∈ ({A, B} : Set (Subgroup G)) := hset ▸ hL
    simpa using this
  rcases hL' with hLA | hLB
  · refine ⟨B, ?_, ?_⟩
    · rw [hLA]; exact hAB.symm
    · rw [hset, hLA]
  · refine ⟨A, ?_, ?_⟩
    · rw [hLB]; exact hAB
    · rw [hset, hLB, Set.pair_comm]

theorem mem_conjSetOf_self (M L : Subgroup G) : L ∈ conjSetOf M L :=
  ⟨1, M.one_mem, by ext x; simp⟩

theorem le_normalizer_of_ncard_conjSetOf_eq_one (h : (conjSetOf M L).ncard = 1) :
    M ≤ normalizer (L : Set G) := by
  intro m hm
  obtain ⟨K, hK⟩ := Set.ncard_eq_one.mp h
  have hLmem : L ∈ conjSetOf M L := mem_conjSetOf_self M L
  have hKL : K = L := by
    have : L ∈ ({K} : Set (Subgroup G)) := hK ▸ hLmem
    exact (Set.mem_singleton_iff.mp this).symm
  have hmap : L.map (MulAut.conj m).toMonoidHom = L := by
    have hmem : L.map (MulAut.conj m).toMonoidHom ∈ conjSetOf M L := ⟨m, hm, rfl⟩
    rw [hK, hKL] at hmem
    exact Set.mem_singleton_iff.mp hmem
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr hmap

theorem two_le_ncard_conjSetOf_of_not_le_normalizer (hnot : ¬ M ≤ normalizer (L : Set G)) :
    2 ≤ (conjSetOf M L).ncard := by
  have hfin : (conjSetOf M L).Finite := Set.toFinite _
  have hpos : 0 < (conjSetOf M L).ncard :=
    (Set.ncard_pos hfin).mpr ⟨L, mem_conjSetOf_self M L⟩
  by_contra h
  exact hnot (le_normalizer_of_ncard_conjSetOf_eq_one (by omega))

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
