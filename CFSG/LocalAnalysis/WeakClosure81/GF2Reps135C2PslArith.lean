module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2PslArithOne
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2PslArithMulti

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open Finset
open CFSG.HardMathSupport.Meierfrankenfeld.PSUScalar

theorem w135c2_psl_classify_three {n f s : ℕ} (hn : 2 ≤ n) (hs : 1 ≤ s)
    (ε : Fin f → Finset (Fin n)) (h0 : ∀ r, (⟨0, by omega⟩ : Fin n) ∉ ε r)
    (hact : ∃ r, ε r ≠ ∅) (hper : f ≤ s * (univ.filter fun r => ε r ≠ ∅).card)
    (hmv : s * movedTop hn ε ≤ 6) :
    (∃ (r₀ : Fin f) (j : Fin n), (∀ r, r ≠ r₀ → ε r = ∅) ∧ ε r₀ = {j} ∧
        ((j : ℕ) = 1 ∨ (j : ℕ) + 1 = n)) ∨
      (n = 4 ∧ f = 1 ∧ s = 1 ∧ ∃ j : Fin n, (j : ℕ) = 2 ∧ ∀ r, ε r = {j}) ∨
      (n = 5 ∧ f = 1 ∧ s = 1 ∧ ∃ j : Fin n, ((j : ℕ) = 2 ∨ (j : ℕ) = 3) ∧ ∀ r, ε r = {j}) ∨
      (n = 3 ∧ f = 1 ∧ s = 1 ∧ ∃ a b : Fin n, (a : ℕ) = 1 ∧ (b : ℕ) = 2 ∧ ∀ r, ε r = {a, b}) ∨
      (n = 2 ∧ f = 2 ∧ s = 1 ∧ ∃ j : Fin n, (j : ℕ) = 1 ∧ ∀ r, ε r = {j}) := by
  classical
  obtain ⟨r₀, hr₀⟩ := hact
  by_cases hone : ∀ r, r ≠ r₀ → ε r = ∅
  · have hcard : (univ.filter fun r => ε r ≠ ∅).card = 1 := by
      rw [Finset.card_eq_one]
      refine ⟨r₀, Finset.ext fun r => ?_⟩
      simp only [mem_filter, mem_univ, true_and, mem_singleton]
      constructor
      · intro hr
        by_contra hne
        exact hr (hone r hne)
      · rintro rfl
        exact hr₀
    rw [hcard, mul_one] at hper
    rcases w135c2_psl_classify_single hn hs ε h0 r₀ hr₀ hone hper hmv with
      ⟨j, hj, hj1⟩ | h | h | h
    · exact Or.inl ⟨r₀, j, hone, hj, hj1⟩
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · obtain ⟨r₂, hr₂'⟩ := not_forall.mp hone
    obtain ⟨hr₂ne, hr₂⟩ := Classical.not_imp.mp hr₂'
    exact Or.inr (Or.inr (Or.inr (Or.inr
      (w135c2_psl_classify_multi hn hs ε h0 r₀ r₂ (Ne.symm hr₂ne) hr₀ hr₂ hper hmv))))

end CFSG.LocalAnalysis.WeakClosure81
