module

public import Mathlib.Tactic.IntervalCases
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Tactic.Positivity.Finset
public import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.RankThree.GF2n.Stroth80

theorem eight_mul_lt_two_pow_add {m : ℕ} (hm : 5 ≤ m) : 8 * m < 2 ^ m + 16 := by
  induction m, hm using Nat.le_induction with
  | base => norm_num
  | succ k hk ih => rw [pow_succ]; omega

theorem sec83_arith {m n a : ℕ} (hm : 2 ≤ m) (ha : 1 ≤ a)
    (hn : 2 * n = a * 2 ^ m + 4 * m + 2)
    (hb : a * 2 ^ m + 4 ≤ 4 * m ∨ a * 2 ^ m + 16 ≤ 8 * m) :
    (m = 2 ∧ a = 1 ∧ n = 7) ∨ (m = 3 ∧ a = 1 ∧ n = 11) ∨ (m = 4 ∧ a = 1 ∧ n = 17) := by
  have hm5 : m < 5 := by
    by_contra h
    have h := not_lt.mp h
    have h1 := eight_mul_lt_two_pow_add h
    have h2 : 2 ^ m ≤ a * 2 ^ m := Nat.le_mul_of_pos_left _ ha
    generalize a * 2 ^ m = P at *
    omega
  interval_cases m
  · norm_num at hn hb
    omega
  · norm_num at hn hb
    omega
  · norm_num at hn hb
    omega

theorem sec83_bound_of_parts {q m x cQ cV cW cV1 cW1 : ℕ} (hq : 2 ≤ q)
    (hV1 : cV1 = q ^ (2 * m + 2)) (hW1 : cW1 = cV1 * q ^ x) (hC : cQ ≤ q ^ (2 * m + 1))
    (hD : cV ^ 2 * cW ≤ cQ * q * cV1)
    (hcases : ((cV = q ^ 2 ∨ cV = q ^ 3) ∧ cW ^ 2 = cV1 * cW1) ∨
      (cV = q ^ 3 ∧ cV1 ^ 3 * cW1 ≤ cW ^ 4)) :
    x + 4 ≤ 4 * m ∨ x + 16 ≤ 8 * m := by
  have hq1 : 1 < q := hq
  have hqpos : 0 < q := by omega
  have hV1pos : 0 < cV1 := by rw [hV1]; positivity
  have hD' : cV ^ 2 * cW ≤ q ^ (2 * m + 2) * cV1 := by
    calc cV ^ 2 * cW ≤ cQ * q * cV1 := hD
      _ ≤ q ^ (2 * m + 1) * q * cV1 := by gcongr
      _ = q ^ (2 * m + 2) * cV1 := by ring
  rcases hcases with ⟨hv, hE⟩ | ⟨hv, hF⟩
  · left
    have hv2 : q ^ 2 ≤ cV := by
      rcases hv with h | h
      · exact h.ge
      · rw [h]; exact Nat.pow_le_pow_right hqpos (by norm_num)
    have h1 : q ^ 4 * cW ≤ q ^ (2 * m + 2) * cV1 := by
      calc q ^ 4 * cW = (q ^ 2) ^ 2 * cW := by ring
        _ ≤ cV ^ 2 * cW := by gcongr
        _ ≤ q ^ (2 * m + 2) * cV1 := hD'
    have h2 : (q ^ 4 * cW) ^ 2 ≤ (q ^ (2 * m + 2) * cV1) ^ 2 := Nat.pow_le_pow_left h1 2
    have h3 : q ^ (8 + x) * cV1 ^ 2 ≤ q ^ (4 * m + 4) * cV1 ^ 2 := by
      calc q ^ (8 + x) * cV1 ^ 2 = q ^ 8 * (cV1 * cW1) := by rw [hW1]; ring
        _ = q ^ 8 * cW ^ 2 := by rw [hE]
        _ = (q ^ 4 * cW) ^ 2 := by ring
        _ ≤ (q ^ (2 * m + 2) * cV1) ^ 2 := h2
        _ = q ^ (4 * m + 4) * cV1 ^ 2 := by ring
    have h4 : q ^ (8 + x) ≤ q ^ (4 * m + 4) := Nat.le_of_mul_le_mul_right h3 (by positivity)
    have h5 := (Nat.pow_le_pow_iff_right hq1).mp h4
    omega
  · right
    rw [hv] at hD'
    have h1 : q ^ 6 * cW ≤ q ^ (2 * m + 2) * cV1 := by
      calc q ^ 6 * cW = (q ^ 3) ^ 2 * cW := by ring
        _ ≤ q ^ (2 * m + 2) * cV1 := hD'
    have h2 : (q ^ 6 * cW) ^ 4 ≤ (q ^ (2 * m + 2) * cV1) ^ 4 := Nat.pow_le_pow_left h1 4
    have h3 : q ^ (24 + x) * cV1 ^ 4 ≤ q ^ (8 * m + 8) * cV1 ^ 4 := by
      calc q ^ (24 + x) * cV1 ^ 4 = q ^ 24 * (cV1 ^ 3 * cW1) := by rw [hW1]; ring
        _ ≤ q ^ 24 * cW ^ 4 := by gcongr
        _ = (q ^ 6 * cW) ^ 4 := by ring
        _ ≤ (q ^ (2 * m + 2) * cV1) ^ 4 := h2
        _ = q ^ (8 * m + 8) * cV1 ^ 4 := by ring
    have h4 : q ^ (24 + x) ≤ q ^ (8 * m + 8) := Nat.le_of_mul_le_mul_right h3 (by positivity)
    have h5 := (Nat.pow_le_pow_iff_right hq1).mp h4
    omega

end CFSG.RankThree.GF2n.Stroth80
