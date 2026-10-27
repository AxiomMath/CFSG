module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2Defs
public import CFSG.HardMathSupport.Meierfrankenfeld.PSUScalar.CaseAnalysis

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open Finset
open CFSG.HardMathSupport.Meierfrankenfeld.PSUScalar

private theorem c2sloutsin_card_le_pred {n : ℕ} (hn : 2 ≤ n) (S : Finset (Fin n))
    (h0 : (⟨0, by omega⟩ : Fin n) ∉ S) : S.card ≤ n - 1 := by
  have h := Finset.card_lt_univ_of_notMem h0
  rw [Fintype.card_fin] at h
  omega

private theorem c2sloutsin_eq_pair_of_card_two {n : ℕ} (hn : n = 3) (S : Finset (Fin n))
    (h0 : (⟨0, by omega⟩ : Fin n) ∉ S) (hcard : 2 ≤ S.card) :
    ∃ a b : Fin n, (a : ℕ) = 1 ∧ (b : ℕ) = 2 ∧ S = {a, b} := by
  have hn2 : 2 ≤ n := by omega
  have hle : S.card ≤ n - 1 := c2sloutsin_card_le_pred hn2 S h0
  let a : Fin n := ⟨1, by omega⟩
  let b : Fin n := ⟨2, by omega⟩
  have hab : a ≠ b := by
    intro h
    have := congrArg Fin.val h
    simp [a, b] at this
  have hpaircard : ({a, b} : Finset (Fin n)).card = 2 :=
    Finset.card_pair_eq_two_iff.mpr hab
  have hsub : S ⊆ ({a, b} : Finset (Fin n)) := by
    intro x hx
    rw [Finset.mem_insert, Finset.mem_singleton]
    have hx0 : (x : ℕ) ≠ 0 := by
      intro h
      have hx' : x = (⟨0, by omega⟩ : Fin n) := Fin.ext (by simpa using h)
      exact h0 (hx' ▸ hx)
    have hxlt : (x : ℕ) < n := x.isLt
    have hx12 : (x : ℕ) = 1 ∨ (x : ℕ) = 2 := by omega
    rcases hx12 with h | h
    · exact Or.inl (show x = a from Fin.ext h)
    · exact Or.inr (show x = b from Fin.ext h)
  have hScard : S.card = 2 := by omega
  have heq : S = {a, b} :=
    Finset.eq_of_subset_of_card_le hsub (by omega)
  exact ⟨a, b, rfl, rfl, heq⟩

private theorem c2sloutsin_s_eq_one_of {s u M : ℕ} (hs : 1 ≤ s) (hsu : s * u ≤ 3)
    (hmv : M ≤ 4 * u) (hM : 5 ≤ M) : s = 1 := by
  have hu2 : 2 ≤ u := by omega
  have h : s * 2 ≤ 3 := le_trans (Nat.mul_le_mul_left s hu2) hsu
  omega

theorem w135c2_psl_outer_single {n f s u : ℕ} (hn : 2 ≤ n) (hs : 1 ≤ s) (hu : 1 ≤ u)
    (hsu : s * u ≤ 3) (ε : Fin f → Finset (Fin n))
    (h0 : ∀ r, (⟨0, by omega⟩ : Fin n) ∉ ε r) (r₀ : Fin f) (hr₀ : ε r₀ ≠ ∅)
    (hone : ∀ r, r ≠ r₀ → ε r = ∅) (hper : f ≤ s) (hdvd : s ∣ f)
    (hmv : movedTop hn ε ≤ 4 * u) :
    (∃ j : Fin n, ε r₀ = {j} ∧ ((j : ℕ) = 1 ∨ (j : ℕ) + 1 = n)) ∨
      (∃ j : Fin n, ε r₀ = {j} ∧
        ((s = 1 ∧ n.choose (j : ℕ) ≤ 3 * gs03Bound .PSL n f) ∨
          ((s = 2 ∨ s = 3) ∧ n.choose (j : ℕ) ≤ gs03Bound .PSL n f))) ∨
      (n = 6 ∧ f = 1 ∧ s = 1 ∧ ∃ j : Fin n, (j : ℕ) = 3 ∧ ε r₀ = {j}) ∨
      (n = 8 ∧ f = 1 ∧ s = 1 ∧ ∃ j : Fin n, ((j : ℕ) = 2 ∨ (j : ℕ) = 6) ∧ ε r₀ = {j}) ∨
      (n = 3 ∧ f = 1 ∧ s = 1 ∧ ∃ a b : Fin n, (a : ℕ) = 1 ∧ (b : ℕ) = 2 ∧ ε r₀ = {a, b}) ∨
      (n = 4 ∧ f = 1) := by
  classical
  have hu3 : u ≤ 3 := by
    have h : 1 * u ≤ s * u := Nat.mul_le_mul_right u hs
    rw [one_mul] at h
    omega
  have hs3 : s ≤ 3 := by
    have h : s * 1 ≤ s * u := Nat.mul_le_mul_left s hu
    rw [mul_one] at h
    omega
  have hf1 : 1 ≤ f := by have := r₀.isLt; omega
  have hsf : s = f := le_antisymm (Nat.le_of_dvd (by omega) hdvd) hper
  have hmt : movedTop hn ε = movedOrbit hn (ε r₀) := movedTop_of_one hn ε r₀ hone
  have hmvS : movedOrbit hn (ε r₀) ≤ 4 * u := by rw [hmt] at hmv; exact hmv
  have hM12 : movedOrbit hn (ε r₀) ≤ 12 := by omega
  have h0r : (⟨0, by omega⟩ : Fin n) ∉ ε r₀ := h0 r₀
  have hcard_le : (ε r₀).card ≤ n - 1 := c2sloutsin_card_le_pred hn (ε r₀) h0r
  by_cases hcard : 2 ≤ (ε r₀).card
  · have hS3 : 3 ≤ (ε r₀).card + 1 := by omega
    have hlow : 2 * (2 * n - 3) ≤ movedOrbit hn (ε r₀) :=
      two_mul_two_mul_sub_three_le_movedOrbit hn h0r hS3
    have hnle4 : n ≤ 4 := by
      have : 2 * (2 * n - 3) ≤ 12 := le_trans hlow hM12
      omega
    have hnge3 : 3 ≤ n := by omega
    have hn34 : n = 3 ∨ n = 4 := by omega
    rcases hn34 with hn3 | hn4
    · have hMge6 : 6 ≤ movedOrbit hn (ε r₀) := by omega
      have hs1 : s = 1 := c2sloutsin_s_eq_one_of hs hsu hmvS (by omega)
      have hf1' : f = 1 := by omega
      obtain ⟨a, b, ha, hb, hSab⟩ := c2sloutsin_eq_pair_of_card_two hn3 (ε r₀) h0r hcard
      exact Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inl ⟨hn3, hf1', hs1, ⟨a, b, ha, hb, hSab⟩⟩))))
    · have hMge10 : 10 ≤ movedOrbit hn (ε r₀) := by omega
      have hs1 : s = 1 := c2sloutsin_s_eq_one_of hs hsu hmvS (by omega)
      have hf1' : f = 1 := by omega
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨hn4, hf1'⟩))))
  · have hScard1 : (ε r₀).card = 1 := by
      have hpos : 0 < (ε r₀).card :=
        Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hr₀)
      omega
    obtain ⟨j, hSj⟩ := Finset.card_eq_one.mp hScard1
    have hj0 : (j : ℕ) ≠ 0 := by
      intro h
      have hmem : (⟨0, by omega⟩ : Fin n) ∈ ({j} : Finset (Fin n)) := by
        rw [Finset.mem_singleton]
        exact (Fin.ext h).symm
      exact h0r (by rw [hSj]; exact hmem)
    have hj1 : 1 ≤ (j : ℕ) := Nat.one_le_iff_ne_zero.mpr hj0
    by_cases hnat : (j : ℕ) = 1 ∨ (j : ℕ) + 1 = n
    · exact Or.inl ⟨j, hSj, hnat⟩
    · have hjne1 : (j : ℕ) ≠ 1 := fun h => hnat (Or.inl h)
      have hjnen : (j : ℕ) + 1 ≠ n := fun h => hnat (Or.inr h)
      have hMval : movedOrbit hn (ε r₀) = 2 * (n - 2).choose (j - 1) := by
        rw [hSj, movedOrbit_singleton hn hj1]
      have hmvJ : 2 * (n - 2).choose (j - 1) ≤ 4 * u := by
        rw [hMval] at hmvS; exact hmvS
      have hM12J : 2 * (n - 2).choose (j - 1) ≤ 12 := by
        rw [hMval] at hM12; exact hM12
      have hj2 : 2 ≤ (j : ℕ) := by omega
      have hjn2 : (j : ℕ) ≤ n - 2 := by have := j.isLt; omega
      have hchoose : n - 2 ≤ (n - 2).choose (j - 1) := by
        apply le_choose
        · omega
        · omega
      have hMlow : 2 * (n - 2) ≤ movedOrbit hn (ε r₀) := by
        rw [hMval]
        exact Nat.mul_le_mul_left 2 hchoose
      have hnle8 : n ≤ 8 := by
        have : 2 * (n - 2) ≤ 12 := le_trans hMlow hM12
        omega
      have hnge4 : 4 ≤ n := by omega
      have hn_cases : n = 4 ∨ n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8 := by omega
      rcases hn_cases with hn4 | hn5 | hn6 | hn7 | hn8
      · have hjval2 : (j : ℕ) = 2 := by omega
        refine Or.inr (Or.inl ⟨j, hSj, ?_⟩)
        by_cases hs1 : s = 1
        · left
          refine ⟨hs1, ?_⟩
          have hf1' : f = 1 := by omega
          rw [hjval2, hn4, hf1']
          decide
        · right
          have hs23 : s = 2 ∨ s = 3 := by omega
          refine ⟨hs23, ?_⟩
          have hfne1 : f ≠ 1 := by omega
          have hA : gs03Bound .PSL 4 f = 6 := by simp [gs03Bound, hfne1]
          rw [hjval2, hn4, hA]
          decide
      · have hMge6 : 6 ≤ movedOrbit hn (ε r₀) := by omega
        have hs1 : s = 1 := c2sloutsin_s_eq_one_of hs hsu hmvS (by omega)
        have hf1' : f = 1 := by omega
        have hjval : (j : ℕ) = 2 ∨ (j : ℕ) = 3 := by omega
        refine Or.inr (Or.inl ⟨j, hSj, Or.inl ⟨hs1, ?_⟩⟩)
        rcases hjval with h | h <;> rw [h, hn5, hf1'] <;> decide
      · have hMge8 : 8 ≤ movedOrbit hn (ε r₀) := by omega
        have hs1 : s = 1 := c2sloutsin_s_eq_one_of hs hsu hmvS (by omega)
        have hf1' : f = 1 := by omega
        have hjval : (j : ℕ) = 2 ∨ (j : ℕ) = 3 ∨ (j : ℕ) = 4 := by omega
        rcases hjval with h2 | h3 | h4
        · refine Or.inr (Or.inl ⟨j, hSj, Or.inl ⟨hs1, ?_⟩⟩)
          rw [h2, hn6, hf1']
          decide
        · exact Or.inr (Or.inr (Or.inl ⟨hn6, hf1', hs1, ⟨j, h3, hSj⟩⟩))
        · refine Or.inr (Or.inl ⟨j, hSj, Or.inl ⟨hs1, ?_⟩⟩)
          rw [h4, hn6, hf1']
          decide
      · have hMge10 : 10 ≤ movedOrbit hn (ε r₀) := by omega
        have hs1 : s = 1 := c2sloutsin_s_eq_one_of hs hsu hmvS (by omega)
        have hf1' : f = 1 := by omega
        have hjval : (j : ℕ) = 2 ∨ (j : ℕ) = 3 ∨ (j : ℕ) = 4 ∨ (j : ℕ) = 5 := by omega
        rcases hjval with h2 | h3 | h4 | h5
        · refine Or.inr (Or.inl ⟨j, hSj, Or.inl ⟨hs1, ?_⟩⟩)
          rw [h2, hn7, hf1']
          decide
        · exfalso
          have hbad : ¬ (2 * (n - 2).choose (j - 1) ≤ 12) := by
            rw [h3, hn7]; decide
          exact hbad hM12J
        · exfalso
          have hbad : ¬ (2 * (n - 2).choose (j - 1) ≤ 12) := by
            rw [h4, hn7]; decide
          exact hbad hM12J
        · refine Or.inr (Or.inl ⟨j, hSj, Or.inl ⟨hs1, ?_⟩⟩)
          rw [h5, hn7, hf1']
          decide
      · have hMge12 : 12 ≤ movedOrbit hn (ε r₀) := by omega
        have hs1 : s = 1 := c2sloutsin_s_eq_one_of hs hsu hmvS (by omega)
        have hf1' : f = 1 := by omega
        have hjval : (j : ℕ) = 2 ∨ (j : ℕ) = 3 ∨ (j : ℕ) = 4 ∨ (j : ℕ) = 5 ∨
            (j : ℕ) = 6 := by omega
        rcases hjval with h2 | h3 | h4 | h5 | h6
        · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hn8, hf1', hs1, ⟨j, Or.inl h2, hSj⟩⟩)))
        · exfalso
          have hbad : ¬ (2 * (n - 2).choose (j - 1) ≤ 12) := by
            rw [h3, hn8]; decide
          exact hbad hM12J
        · exfalso
          have hbad : ¬ (2 * (n - 2).choose (j - 1) ≤ 12) := by
            rw [h4, hn8]; decide
          exact hbad hM12J
        · exfalso
          have hbad : ¬ (2 * (n - 2).choose (j - 1) ≤ 12) := by
            rw [h5, hn8]; decide
          exact hbad hM12J
        · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hn8, hf1', hs1, ⟨j, Or.inr h6, hSj⟩⟩)))

end CFSG.LocalAnalysis.WeakClosure81
