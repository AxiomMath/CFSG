module

public import Mathlib.GroupTheory.OrderOfElement

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

variable {G : Type*} [Group G] [DecidableEq G]

@[expose] def S16C11AltWords (gens : List G) : ℕ → Finset G
  | 0 => {1}
  | k + 1 => S16C11AltWords gens k ∪
      (S16C11AltWords gens k).biUnion fun x => (gens.map (x * ·)).toFinset

theorem s16c11_alt_words_subset_succ (gens : List G) (k : ℕ) :
    S16C11AltWords gens k ⊆ S16C11AltWords gens (k + 1) :=
  Finset.subset_union_left

theorem s16c11_alt_words_mono (gens : List G) {j k : ℕ} (h : j ≤ k) :
    S16C11AltWords gens j ⊆ S16C11AltWords gens k := by
  induction k, h using Nat.le_induction with
  | base => exact fun x hx => hx
  | succ k _ ih => exact ih.trans (s16c11_alt_words_subset_succ gens k)

theorem s16c11_alt_one_mem_words (gens : List G) (k : ℕ) : (1 : G) ∈ S16C11AltWords gens k :=
  s16c11_alt_words_mono gens (Nat.zero_le k) (Finset.mem_singleton_self 1)

theorem s16c11_alt_mul_mem_words_succ (gens : List G) {k : ℕ} {x g : G}
    (hx : x ∈ S16C11AltWords gens k) (hg : g ∈ gens) :
    x * g ∈ S16C11AltWords gens (k + 1) := by
  refine Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨x, hx, ?_⟩)
  exact List.mem_toFinset.2 (List.mem_map.2 ⟨g, hg, rfl⟩)

theorem s16c11_alt_words_subset_closure (gens : List G) (k : ℕ) :
    (↑(S16C11AltWords gens k) : Set G) ⊆ (Subgroup.closure {g | g ∈ gens} : Set G) := by
  induction k with
  | zero =>
    intro x hx
    have hx1 : x = 1 := by simpa [S16C11AltWords] using hx
    rw [hx1]
    exact (Subgroup.closure {g | g ∈ gens}).one_mem
  | succ k ih =>
    intro x hx
    rcases Finset.mem_union.1 hx with h | h
    · exact ih h
    · obtain ⟨y, hy, hxy⟩ := Finset.mem_biUnion.1 h
      obtain ⟨g, hg, rfl⟩ := List.mem_map.1 (List.mem_toFinset.1 hxy)
      exact (Subgroup.closure {g | g ∈ gens}).mul_mem (ih hy)
        (Subgroup.subset_closure hg)

theorem s16c11_alt_closure_subset_words [Finite G] (gens : List G) (k : ℕ)
    (hfix : S16C11AltWords gens (k + 1) = S16C11AltWords gens k) :
    (Subgroup.closure {g | g ∈ gens} : Set G) ⊆ ↑(S16C11AltWords gens k) := by
  intro x hx
  have hx' : x ∈ Submonoid.closure {g | g ∈ gens} := by
    rw [← Subgroup.closure_toSubmonoid_of_finite]
    exact hx
  clear hx
  induction hx' using Submonoid.closure_induction_right with
  | one => exact s16c11_alt_one_mem_words gens k
  | mul_right x _ y hy ih =>
    have h1 : x * y ∈ S16C11AltWords gens (k + 1) :=
      s16c11_alt_mul_mem_words_succ gens ih hy
    rw [hfix] at h1
    exact h1

theorem s16c11_alt_mem_closure_iff [Finite G] (gens : List G) (k : ℕ)
    (hfix : S16C11AltWords gens (k + 1) = S16C11AltWords gens k) (x : G) :
    x ∈ Subgroup.closure {g | g ∈ gens} ↔ x ∈ S16C11AltWords gens k :=
  ⟨fun h => s16c11_alt_closure_subset_words gens k hfix h,
    fun h => s16c11_alt_words_subset_closure gens k h⟩

theorem s16c11_alt_card_closure [Finite G] (gens : List G) (k : ℕ)
    (hfix : S16C11AltWords gens (k + 1) = S16C11AltWords gens k) :
    Nat.card (Subgroup.closure {g | g ∈ gens}) = (S16C11AltWords gens k).card := by
  calc Nat.card (Subgroup.closure {g | g ∈ gens})
      = Nat.card {x : G // x ∈ S16C11AltWords gens k} := by
        refine Nat.card_congr (Equiv.subtypeEquivRight fun x => ?_)
        exact ⟨fun h => s16c11_alt_closure_subset_words gens k hfix h,
          fun h => s16c11_alt_words_subset_closure gens k h⟩
    _ = (S16C11AltWords gens k).card := Nat.card_eq_finsetCard _

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
