module

public import CFSG.HardMathSupport.Meierfrankenfeld.PSUScalar.CaseAnalysis

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open Finset
open CFSG.HardMathSupport.Meierfrankenfeld.PSUScalar

private theorem c2slone_card_le_pred {n : ℕ} (hn : 2 ≤ n) (S : Finset (Fin n))
    (h0 : (⟨0, by omega⟩ : Fin n) ∉ S) : S.card ≤ n - 1 := by
  have h := Finset.card_lt_univ_of_notMem h0
  rw [Fintype.card_fin] at h
  omega

private theorem c2slone_eq_pair_of_card_two {n : ℕ} (hn : n = 3) (S : Finset (Fin n))
    (h0 : (⟨0, by omega⟩ : Fin n) ∉ S) (hcard : 2 ≤ S.card) :
    ∃ a b : Fin n, (a : ℕ) = 1 ∧ (b : ℕ) = 2 ∧ S = {a, b} := by
  have hn2 : 2 ≤ n := by omega
  have hle : S.card ≤ n - 1 := c2slone_card_le_pred hn2 S h0
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

theorem w135c2_psl_classify_single {n f s : ℕ} (hn : 2 ≤ n) (hs : 1 ≤ s)
    (ε : Fin f → Finset (Fin n)) (h0 : ∀ r, (⟨0, by omega⟩ : Fin n) ∉ ε r)
    (r₀ : Fin f) (hr₀ : ε r₀ ≠ ∅) (hone : ∀ r, r ≠ r₀ → ε r = ∅) (hper : f ≤ s)
    (hmv : s * movedTop hn ε ≤ 6) :
    (∃ j : Fin n, ε r₀ = {j} ∧ ((j : ℕ) = 1 ∨ (j : ℕ) + 1 = n)) ∨
      (n = 4 ∧ f = 1 ∧ s = 1 ∧ ∃ j : Fin n, (j : ℕ) = 2 ∧ ∀ r, ε r = {j}) ∨
      (n = 5 ∧ f = 1 ∧ s = 1 ∧ ∃ j : Fin n, ((j : ℕ) = 2 ∨ (j : ℕ) = 3) ∧ ∀ r, ε r = {j}) ∨
      (n = 3 ∧ f = 1 ∧ s = 1 ∧ ∃ a b : Fin n, (a : ℕ) = 1 ∧ (b : ℕ) = 2 ∧ ∀ r, ε r = {a, b}) := by
  classical
  have hmt : movedTop hn ε = movedOrbit hn (ε r₀) := movedTop_of_one hn ε r₀ hone
  have hmvS : s * movedOrbit hn (ε r₀) ≤ 6 := by rw [hmt] at hmv; exact hmv
  have hM6 : movedOrbit hn (ε r₀) ≤ 6 := by
    calc movedOrbit hn (ε r₀) = 1 * movedOrbit hn (ε r₀) := (one_mul _).symm
      _ ≤ s * movedOrbit hn (ε r₀) := Nat.mul_le_mul_right _ hs
      _ ≤ 6 := hmvS
  have h0r : (⟨0, by omega⟩ : Fin n) ∉ ε r₀ := h0 r₀
  have hcard_le : (ε r₀).card ≤ n - 1 := c2slone_card_le_pred hn (ε r₀) h0r
  by_cases hcard : 2 ≤ (ε r₀).card
  · have hS3 : 3 ≤ (ε r₀).card + 1 := by omega
    have hlow : 2 * (2 * n - 3) ≤ movedOrbit hn (ε r₀) :=
      two_mul_two_mul_sub_three_le_movedOrbit hn h0r hS3
    have hnle3 : n ≤ 3 := by
      have : 2 * (2 * n - 3) ≤ 6 := le_trans hlow hM6
      omega
    have hnge3 : 3 ≤ n := by omega
    have hn3 : n = 3 := by omega
    have hMge : 6 ≤ movedOrbit hn (ε r₀) := by omega
    have hM6eq : movedOrbit hn (ε r₀) = 6 := le_antisymm hM6 hMge
    have hs1 : s = 1 := by
      have h : s * 6 ≤ 6 := by
        calc s * 6 = s * movedOrbit hn (ε r₀) := by rw [hM6eq]
          _ ≤ 6 := hmvS
      omega
    have hf1 : f = 1 := by
      have h1 : 1 ≤ f := by have := r₀.isLt; omega
      omega
    obtain ⟨a, b, ha, hb, hSab⟩ := c2slone_eq_pair_of_card_two hn3 (ε r₀) h0r hcard
    have hall : ∀ r : Fin f, ε r = {a, b} := by
      intro r
      have hr : r = r₀ := Fin.ext (by have := r.isLt; have := r₀.isLt; omega)
      rw [hr, hSab]
    exact Or.inr (Or.inr (Or.inr ⟨hn3, hf1, hs1, ⟨a, b, ha, hb, hall⟩⟩))
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
      have hmvJ : s * (2 * (n - 2).choose (j - 1)) ≤ 6 := by
        rw [hMval] at hmvS; exact hmvS
      have hM6J : 2 * (n - 2).choose (j - 1) ≤ 6 := by
        rw [hMval] at hM6; exact hM6
      have hj2 : 2 ≤ (j : ℕ) := by omega
      have hjn2 : (j : ℕ) ≤ n - 2 := by have := j.isLt; omega
      have hchoose : n - 2 ≤ (n - 2).choose (j - 1) := by
        apply le_choose
        · omega
        · omega
      have hnle5 : n ≤ 5 := by
        have h2 : 2 * (n - 2) ≤ 2 * (n - 2).choose (j - 1) :=
          Nat.mul_le_mul_left 2 hchoose
        omega
      have hnge4 : 4 ≤ n := by omega
      have hM4 : 4 ≤ 2 * (n - 2).choose (j - 1) := by
        have h2 : 2 * (n - 2) ≤ 2 * (n - 2).choose (j - 1) :=
          Nat.mul_le_mul_left 2 hchoose
        omega
      have hs1 : s = 1 := by
        have h4 : s * 4 ≤ 6 := by
          calc s * 4 ≤ s * (2 * (n - 2).choose (j - 1)) := Nat.mul_le_mul_left s hM4
            _ ≤ 6 := hmvJ
        omega
      have hf1 : f = 1 := by
        have h1 : 1 ≤ f := by have := r₀.isLt; omega
        omega
      have hall : ∀ r : Fin f, ε r = {j} := by
        intro r
        have hr : r = r₀ := Fin.ext (by have := r.isLt; have := r₀.isLt; omega)
        rw [hr, hSj]
      have hn45 : n = 4 ∨ n = 5 := by omega
      rcases hn45 with hn4 | hn5
      · refine Or.inr (Or.inl ⟨hn4, hf1, hs1, ⟨j, ?_, hall⟩⟩)
        omega
      · refine Or.inr (Or.inr (Or.inl ⟨hn5, hf1, hs1, ⟨j, ?_, hall⟩⟩))
        omega

end CFSG.LocalAnalysis.WeakClosure81
