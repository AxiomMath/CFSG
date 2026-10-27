module

public import CFSG.Open.Defs

public section

namespace CFSG.Open

@[expose] def gorensteinHarada74Orders : Set ℕ :=
  {m | ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧
      (m = ordG2 (p ^ f) ∨ m = ordTrialityD4 (p ^ f) ∨ m = ordBC 2 (p ^ f) ∨
        (p ^ f % 8 ≠ 1 ∧ m = ordA 3 (p ^ f)) ∨
        (p ^ f % 8 ≠ 7 ∧ m = ordTwistedA 3 (p ^ f)) ∨
        (p ^ f % 4 = 3 ∧ m = ordA 4 (p ^ f)) ∨
        (p ^ f % 4 = 1 ∧ m = ordTwistedA 4 (p ^ f)))} ∪
  {m | ∃ k : ℕ, 1 ≤ k ∧ m = ordRee (3 ^ (2 * k + 1))} ∪
  {ordA 1 8, ordA 1 16, ordA 2 4, ordSuzuki 8} ∪
  {m | ∃ n : ℕ, 8 ≤ n ∧ n ≤ 11 ∧ m = Nat.factorial n / 2} ∪
  {2 ^ 6 * 3 ^ 3 * 5 * 11, 2 ^ 7 * 3 ^ 2 * 5 * 7 * 11, 2 ^ 7 * 3 ^ 2 * 5 * 7 * 11 * 23,
    2 ^ 3 * 3 * 5 * 7 * 11 * 19, 2 ^ 7 * 3 ^ 3 * 5 ^ 2 * 7, 2 ^ 7 * 3 ^ 5 * 5 * 17 * 19,
    2 ^ 7 * 3 ^ 6 * 5 ^ 3 * 7 * 11, 2 ^ 8 * 3 ^ 7 * 5 ^ 6 * 7 * 11 * 31 * 37 * 67}

end CFSG.Open
