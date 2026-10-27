module

public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.RankThree.PartTwo.Sec4

theorem not_five_dvd_su_three_order {n : ℕ} (hn : Odd n) :
    ¬ 5 ∣ (2 ^ n) ^ 3 * ((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 3 + 1) := by
  obtain ⟨k, rfl⟩ := hn
  have hq : (2 ^ (2 * k + 1)) % 5 = 2 ∨ (2 ^ (2 * k + 1)) % 5 = 3 := by
    induction k with
    | zero => simp
    | succ m ih =>
      have : 2 ^ (2 * (m + 1) + 1) = 2 ^ (2 * m + 1) * 4 := by ring
      rw [this]; omega
  have hp : Nat.Prime 5 := by norm_num
  intro h
  generalize 2 ^ (2 * k + 1) = q at hq h
  rcases (Nat.Prime.dvd_mul hp).mp h with h1 | h3
  · rcases (Nat.Prime.dvd_mul hp).mp h1 with h2 | h2
    · have := hp.dvd_of_dvd_pow h2
      omega
    · have hq1 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ (by omega)
      have : (q ^ 2 - 1) % 5 = 3 := by
        have : q ^ 2 % 5 = 4 := by
          rcases hq with h | h <;> simp [pow_two, Nat.mul_mod, h]
        omega
      omega
  · have : (q ^ 3 + 1) % 5 = 4 ∨ (q ^ 3 + 1) % 5 = 3 := by
      rcases hq with h | h <;> simp [pow_succ, Nat.mul_mod, Nat.add_mod, h]
    omega

end CFSG.RankThree.PartTwo.Sec4
