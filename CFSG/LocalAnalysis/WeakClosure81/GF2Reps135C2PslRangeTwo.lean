module

import Mathlib.Tactic.IntervalCases
public import CFSG.HardMathSupport.Meierfrankenfeld.PSUScalar.WeylOrbitBounds
public import Mathlib.Tactic.FinCases

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open Finset
open CFSG.HardMathSupport.Meierfrankenfeld.PSUScalar

private lemma c2slr2_eq_empty_or_singleton {f : ℕ} {ε : Fin f → Finset (Fin 2)}
    (h0 : ∀ r, (0 : Fin 2) ∉ ε r) (r : Fin f) :
    ε r = ∅ ∨ ε r = {1} := by
  rcases Finset.eq_empty_or_nonempty (ε r) with h | ⟨x, hx⟩
  · exact Or.inl h
  · refine Or.inr ?_
    have hx1 : x = 1 := by
      fin_cases x
      · exact absurd hx (h0 r)
      · rfl
    rw [hx1] at hx
    exact Finset.eq_singleton_iff_unique_mem.mpr ⟨hx, fun b hb => by
      fin_cases b
      · exact absurd hb (h0 r)
      · rfl⟩

private lemma c2slr2_eq_singleton_of_ne_empty {f : ℕ} {ε : Fin f → Finset (Fin 2)}
    (h0 : ∀ r, (0 : Fin 2) ∉ ε r) {r : Fin f} (h : ε r ≠ ∅) : ε r = {1} := by
  rcases c2slr2_eq_empty_or_singleton h0 r with he | he
  · exact absurd he h
  · exact he

private lemma c2slr2_fin_two_ne {s : ℕ} {ε : Fin 2 → Finset (Fin 2)}
    (hmin : ∀ p : ℕ, 0 < p → p < s →
      ∃ r : Fin 2, ε ⟨(r + p) % 2, Nat.mod_lt _ r.pos⟩ ≠ ε r)
    (hs : 1 < s) :
    ε (0 : Fin 2) ≠ ε (1 : Fin 2) := by
  obtain ⟨r, hr⟩ := hmin 1 (by norm_num) hs
  fin_cases r
  · have h10 : ε (1 : Fin 2) ≠ ε (0 : Fin 2) := by simpa using hr
    exact h10.symm
  · have h01 : ε (0 : Fin 2) ≠ ε (1 : Fin 2) := by simpa using hr
    exact h01

theorem w135c2_psl_range_two {f s d : ℕ}
    (hs : 1 ≤ s) (ε : Fin f → Finset (Fin 2))
    (h0 : ∀ r, (⟨0, by omega⟩ : Fin 2) ∉ ε r) (hact : ∃ r, ε r ≠ ∅)
    (hper : f ≤ s * (univ.filter fun r => ε r ≠ ∅).card)
    (hrot : ∀ r : Fin f, ε ⟨(r + s) % f, Nat.mod_lt _ r.pos⟩ = ε r)
    (hmin : ∀ p : ℕ, 0 < p → p < s → ∃ r : Fin f, ε ⟨(r + p) % f, Nat.mod_lt _ r.pos⟩ ≠ ε r)
    (hd : d = 2 ^ (univ.filter fun r => ε r ≠ ∅).card)
    (hrange : (s = 1 ∧ d ≤ 3 * (if Even f then 4 else 3)) ∨
      ((s = 2 ∨ s = 3) ∧ d ≤ if Even f then 4 else 3)) :
    s * d < 4 * f := by
  classical
  have hzero : ∀ r, (0 : Fin 2) ∉ ε r := by
    intro r hr
    exact h0 r (by simpa using hr)
  have hcard_le : (univ.filter fun r => ε r ≠ ∅).card ≤ f :=
    calc (univ.filter fun r => ε r ≠ ∅).card ≤ (univ : Finset (Fin f)).card :=
          Finset.card_le_card (Finset.filter_subset _ _)
      _ = f := by simp
  have hd_le : d ≤ 2 ^ f := by
    rw [hd]
    exact Nat.pow_le_pow_right (by norm_num) hcard_le
  have h12 : s * d ≤ 12 := by
    have hA : (if Even f then (4 : ℕ) else 3) ≤ 4 := by split <;> omega
    rcases hrange with ⟨hs1, hd1⟩ | ⟨hs23, hd23⟩
    · subst hs1
      omega
    · rcases hs23 with hs2 | hs3
      · subst hs2; omega
      · subst hs3; omega
  by_cases hf3 : f ≤ 3
  · interval_cases f
    ·
      obtain ⟨r, -⟩ := hact
      exact absurd r.pos (by omega)
    ·
      by_cases hs1 : s = 1
      · subst hs1
        have hd2 : d ≤ 2 ^ 1 := by simpa using hd_le
        omega
      · have hs2 : 1 < s := by omega
        obtain ⟨r, hr⟩ := hmin 1 (by norm_num) hs2
        have harg : (⟨(r + 1) % 1, Nat.mod_lt _ r.pos⟩ : Fin 1) = r := by
          apply Fin.ext
          have := r.isLt
          simp only [Nat.mod_one]
          omega
        rw [harg] at hr
        exact absurd rfl hr
    ·
      by_cases hs1 : s = 1
      · subst hs1
        have hd4 : d ≤ 2 ^ 2 := by simpa using hd_le
        omega
      · have hs2 : 1 < s := by omega
        have hs23 : s = 2 ∨ s = 3 := by
          rcases hrange with ⟨h, -⟩ | ⟨h, -⟩
          · exact absurd h hs1
          · exact h
        rcases hs23 with hs2eq | hs3eq
        · subst hs2eq
          have hne : ε (0 : Fin 2) ≠ ε (1 : Fin 2) :=
            c2slr2_fin_two_ne hmin (by norm_num : 1 < 2)
          have hle1 : (univ.filter fun r => ε r ≠ ∅).card ≤ 1 := by
            rw [Finset.card_le_one]
            intro a ha b hb
            rw [Finset.mem_filter] at ha hb
            have hae : ε a = {1} := c2slr2_eq_singleton_of_ne_empty hzero ha.2
            have hbe : ε b = {1} := c2slr2_eq_singleton_of_ne_empty hzero hb.2
            have heq : ε a = ε b := by rw [hae, hbe]
            by_contra hab
            fin_cases a <;> fin_cases b <;> simp_all
          have hd2 : d ≤ 2 := by
            rw [hd]
            calc 2 ^ (univ.filter fun r => ε r ≠ ∅).card ≤ 2 ^ 1 :=
                  Nat.pow_le_pow_right (by norm_num) hle1
              _ = 2 := by norm_num
          omega
        · subst hs3eq
          have hrot1 : ∀ r : Fin 2, ε ⟨(r + 1) % 2, Nat.mod_lt _ r.pos⟩ = ε r := by
            intro r
            have h := hrot r
            have harg : (⟨(r + 1) % 2, Nat.mod_lt _ r.pos⟩ : Fin 2)
                = (⟨(r + 3) % 2, Nat.mod_lt _ r.pos⟩ : Fin 2) := by
              apply Fin.ext
              fin_cases r <;> norm_num
            rw [harg]
            exact h
          obtain ⟨r, hr⟩ := hmin 1 (by norm_num) (by norm_num : 1 < 3)
          exact absurd (hrot1 r) hr
    ·
      rcases hrange with ⟨hs1, hd1⟩ | ⟨hs23, hd23⟩
      · subst hs1
        have hd8 : d ≤ 2 ^ 3 := by simpa using hd_le
        omega
      · have hif3 : (if Even 3 then (4 : ℕ) else 3) = 3 := by decide
        have hd3 : d ≤ 3 := by rw [hif3] at hd23; exact hd23
        rcases hs23 with hs2 | hs3
        · subst hs2; omega
        · subst hs3; omega
  · have hf4 : 4 ≤ f := by omega
    omega

end CFSG.LocalAnalysis.WeakClosure81
