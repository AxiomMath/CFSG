module

public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Finset

public section

namespace CFSG.OddTranspositions.PartFour

theorem lemma16_3_one {x y a : ℕ} (h : y ^ 2 + 2 ^ a = x ^ 2) :
    ∃ b c : ℕ, b ≤ c ∧ b + c = a ∧ 2 * x = 2 ^ b + 2 ^ c ∧ 2 * y + 2 ^ b = 2 ^ c := by
  have hyx : y ≤ x := by
    have h2 : y ^ 2 ≤ x ^ 2 := by
      calc y ^ 2 ≤ y ^ 2 + 2 ^ a := Nat.le_add_right _ _
        _ = x ^ 2 := h
    exact Nat.mul_self_le_mul_self_iff.mp (by simpa [pow_two] using h2)
  have hde : (x + y) * (x - y) = 2 ^ a := by
    rw [← Nat.sq_sub_sq]
    exact Nat.sub_eq_of_eq_add' h.symm
  have hdvd : x - y ∣ 2 ^ a := ⟨x + y, by rw [mul_comm]; exact hde.symm⟩
  obtain ⟨b, hba, hb⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  have hevd : x + y ∣ 2 ^ a := ⟨x - y, hde.symm⟩
  obtain ⟨c, hca, hc⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hevd
  have hdle : x - y ≤ x + y := by omega
  have hbc : b ≤ c := by
    apply (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp
    simpa [hb, hc] using hdle
  have hbca : b + c = a := by
    have h' : 2 ^ (b + c) = 2 ^ a := by
      rw [pow_add, ← hb, ← hc]
      simpa only [mul_comm] using hde
    exact Nat.pow_right_injective (by norm_num : 2 ≤ 2) h'
  refine ⟨b, c, hbc, hbca, by omega, by omega⟩

end CFSG.OddTranspositions.PartFour
