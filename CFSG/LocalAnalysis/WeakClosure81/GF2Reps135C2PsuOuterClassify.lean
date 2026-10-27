module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2PsuOuterMulti
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2PsuOuterSingle

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open Finset
open CFSG.HardMathSupport.Meierfrankenfeld.PSUScalar

theorem w135c2_psu_classify_outer {n f s u : ℕ} (hn : 3 ≤ n) (hn4 : n ≠ 4)
    (hnf : ¬ (n = 3 ∧ f = 1)) (hs : 1 ≤ s) (hu : 1 ≤ u) (hsu : s * u ≤ 3)
    (ε : Fin f → Finset (Fin n)) (h0 : ∀ r, (⟨0, by omega⟩ : Fin n) ∉ ε r)
    (hact : ∃ r, ε r ≠ ∅) (hper : f ≤ s * (univ.filter fun r => ε r ≠ ∅).card)
    (hns : (univ.filter fun r => ε r ≠ ∅).card ≤ 2 →
      (∃ r, (ε r).image labelStar ≠ ε r) → 2 * f ≤ s)
    (hmv : movedTop (by omega : 2 ≤ n) ε ≤ 4 * u) :
    (∃ (r₀ : Fin f) (j : Fin n), (∀ r, r ≠ r₀ → ε r = ∅) ∧ ε r₀ = {j} ∧
        ((j : ℕ) = 1 ∨ (j : ℕ) + 1 = n) ∧ f = 1) ∨
      (n = 6 ∧ f = 1 ∧ s = 1 ∧ u = 3 ∧ ∃ (r₀ : Fin f) (j : Fin n),
        (∀ r, r ≠ r₀ → ε r = ∅) ∧ (j : ℕ) = 3 ∧ ε r₀ = {j}) := by
  classical
  obtain ⟨r₀, hr₀⟩ := hact
  by_cases hone : ∀ r, r ≠ r₀ → ε r = ∅
  · have hsub : (univ.filter fun r => ε r ≠ ∅) ⊆ {r₀} := by
      intro r hr
      rw [Finset.mem_singleton]
      by_contra hne
      exact (Finset.mem_filter.mp hr).2 (hone r hne)
    have hc1 := Finset.card_le_card hsub
    rw [Finset.card_singleton] at hc1
    have hper' : f ≤ s := hper.trans (by simpa using Nat.mul_le_mul_left s hc1)
    have hns' : (∃ r, (ε r).image labelStar ≠ ε r) → 2 * f ≤ s :=
      hns (hc1.trans (by norm_num))
    rcases w135c2_psu_outer_single hn hn4 hnf hs hu hsu ε h0 r₀ hr₀ hone hper' hns' hmv with
      ⟨j, hj, hjn, hf⟩ | ⟨h6, hf, hs1, hu3, j, hj3, hj⟩
    · exact Or.inl ⟨r₀, j, hone, hj, hjn, hf⟩
    · exact Or.inr ⟨h6, hf, hs1, hu3, r₀, j, hone, hj3, hj⟩
  · push Not at hone
    obtain ⟨r₁, hr₁, hne⟩ := hone
    exact (w135c2_psu_outer_multi hn hs hu hsu ε h0 r₀ r₁ (Ne.symm hr₁) hr₀ hne.ne_empty hper
      hns hmv).elim

end CFSG.LocalAnalysis.WeakClosure81
