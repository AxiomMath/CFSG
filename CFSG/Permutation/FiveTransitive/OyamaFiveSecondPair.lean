module

public import CFSG.Permutation.FiveTransitive.StableInvolutionPairs

public section

namespace CFSG

namespace FiveTransitive.OyamaFiveSecondPair

open MulAction FixedFiveInvolutionGeometry StableInvolutionPairs

theorem coordinates
    {G X : Type*} [Group G] [Finite X] [MulAction G X]
    (hmax : ∀ g : G, g * g = 1 → g ≠ 1 → (fixedBy X g).ncard ≤ 5)
    (e : Fin 9 ↪ X) (a b c : G) (hc : c * c = 1) (hc1 : c ≠ 1)
    (hac : a * c = c * a) (hbc : b * c = c * b)
    (hfixa : fixedBy X a = {e 0, e 1, e 2, e 3, e 4})
    (hfixb : fixedBy X b = {e 0, e 5, e 6, e 7, e 8})
    (hc1fix : c • e 1 = e 1) (hc2fix : c • e 2 = e 2)
    (hc5fix : c • e 5 = e 5) (hc6fix : c • e 6 = e 6) :
    fixedBy X c = {e 0, e 1, e 2, e 5, e 6} ∧ c • e 0 = e 0 ∧
      c • e 3 = e 4 ∧ c • e 4 = e 3 ∧ c • e 7 = e 8 ∧ c • e 8 = e 7 := by
  have hinter : fixedBy X a ∩ fixedBy X b = {e 0} := by
    rw [hfixa, hfixb]
    ext z
    simp only [Set.mem_inter_iff, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨h, k⟩
      rcases h with h | h | h | h | h <;> rcases k with k | k | k | k | k <;>
        simp_all [e.injective.eq_iff]
    · intro h; exact ⟨Or.inl h, Or.inl h⟩
  have hc0 := fixes_singleton_intersection a b c hac hbc (e 0) hinter
  have hfixc : fixedBy X c = {e 0, e 1, e 2, e 5, e 6} := by
    apply fixedBy_eq_of_five c (hmax c hc hc1)
    · simp [e.injective.eq_iff]
    · intro z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl | rfl | rfl | rfl
      · exact hc0
      · exact hc1fix
      · exact hc2fix
      · exact hc5fix
      · exact hc6fix
  have hdiffa : fixedBy X a \ fixedBy X c = {e 3, e 4} := by
    rw [hfixa, hfixc]
    ext z
    simp only [Set.mem_sdiff, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨h, hn⟩
      rcases h with h | h | h | h | h
      · exact (hn (Or.inl h)).elim
      · exact (hn (Or.inr (Or.inl h))).elim
      · exact (hn (Or.inr (Or.inr (Or.inl h)))).elim
      · exact Or.inl h
      · exact Or.inr h
    · rintro (rfl | rfl) <;> simp [e.injective.eq_iff]
  have hdiffb : fixedBy X b \ fixedBy X c = {e 7, e 8} := by
    rw [hfixb, hfixc]
    ext z
    simp only [Set.mem_sdiff, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨h, hn⟩
      rcases h with h | h | h | h | h
      · exact (hn (Or.inl h)).elim
      · exact (hn (Or.inr (Or.inr (Or.inr (Or.inl h))))).elim
      · exact (hn (Or.inr (Or.inr (Or.inr (Or.inr h))))).elim
      · exact Or.inl h
      · exact Or.inr h
    · rintro (rfl | rfl) <;> simp [e.injective.eq_iff]
  have hcc : ∀ z ∈ fixedBy X c, c • z ∈ fixedBy X c := by
    intro z hz
    simpa only [show c • z = z from hz] using hz
  have h34stable : ∀ z ∈ ({e 3, e 4} : Set X), c • z ∈ ({e 3, e 4} : Set X) := by
    rw [← hdiffa]
    exact preserves_diff c hc _ _ (fun _ hz => mem_fixedBy_smul_of_commute a c hac hz) hcc
  have h78stable : ∀ z ∈ ({e 7, e 8} : Set X), c • z ∈ ({e 7, e 8} : Set X) := by
    rw [← hdiffb]
    exact preserves_diff c hc _ _ (fun _ hz => mem_fixedBy_smul_of_commute b c hbc hz) hcc
  have h3ne : c • e 3 ≠ e 3 := by
    intro h
    have hm : e 3 ∈ fixedBy X c := h
    rw [hfixc] at hm
    simp [e.injective.eq_iff] at hm
  have h7ne : c • e 7 ≠ e 7 := by
    intro h
    have hm : e 7 ∈ fixedBy X c := h
    rw [hfixc] at hm
    simp [e.injective.eq_iff] at hm
  exact ⟨hfixc, hc0, (swap_pair c hc _ _ h34stable h3ne).1,
    (swap_pair c hc _ _ h34stable h3ne).2,
    (swap_pair c hc _ _ h78stable h7ne).1, (swap_pair c hc _ _ h78stable h7ne).2⟩

end FiveTransitive.OyamaFiveSecondPair

end CFSG
