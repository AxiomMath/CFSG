module

public import Mathlib.Data.Int.ModEq
public import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.NumberTheory

theorem exists_sign_mod_four_odd_cofactors {q : ℕ} (hq : Odd q) :
    ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ (q : ℤ) ≡ ε [ZMOD 4] ∧
      ∃ m n h : ℕ, (m : ℤ) = (q : ℤ) - ε ∧
        (q : ℤ) + ε = 2 * (n : ℤ) ∧ Odd n ∧
        (q : ℤ) ^ 2 + 1 = 2 * (h : ℤ) ∧ Odd h := by
  rcases Nat.odd_mod_four_iff.mp (Nat.odd_iff.mp hq) with hq1 | hq3
  ·
    obtain ⟨k, rfl⟩ : ∃ k, q = 4 * k + 1 := by
      refine ⟨q / 4, ?_⟩
      have := Nat.div_add_mod q 4
      omega
    refine ⟨1, Or.inl rfl, ?_, 4 * k, 2 * k + 1, 8 * k * k + 4 * k + 1,
      ?_, ?_, ⟨k, by ring⟩, ?_, ⟨4 * k * k + 2 * k, by ring⟩⟩
    · rw [Int.modEq_iff_dvd]
      refine ⟨-(k : ℤ), ?_⟩
      push_cast
      ring
    · push_cast
      ring
    · push_cast
      ring
    · push_cast
      ring
  ·
    obtain ⟨k, rfl⟩ : ∃ k, q = 4 * k + 3 := by
      refine ⟨q / 4, ?_⟩
      have := Nat.div_add_mod q 4
      omega
    refine ⟨-1, Or.inr rfl, ?_, 4 * k + 4, 2 * k + 1, 8 * k * k + 12 * k + 5,
      ?_, ?_, ⟨k, by ring⟩, ?_, ⟨4 * k * k + 6 * k + 2, by ring⟩⟩
    · rw [Int.modEq_iff_dvd]
      refine ⟨-((k : ℤ) + 1), ?_⟩
      push_cast
      ring
    · push_cast
      ring
    · push_cast
      ring
    · push_cast
      ring

end CFSG.NumberTheory

end
