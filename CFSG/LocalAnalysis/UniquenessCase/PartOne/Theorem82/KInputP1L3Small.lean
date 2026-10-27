module

public import CFSG.HardMathSupport.Solomon.Coordinator.I14_20LieOrd

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82

theorem psl3_ge_of_five_le {q : ℕ} (hq : 5 ≤ q) :
    372000 ≤ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1)) := by
  have h2 : 5 ^ 2 ≤ q ^ 2 := Nat.pow_le_pow_left hq 2
  have h3 : 5 ^ 3 ≤ q ^ 3 := Nat.pow_le_pow_left hq 3
  calc 372000 = 5 ^ 3 * ((5 ^ 2 - 1) * (5 ^ 3 - 1)) := by norm_num
    _ ≤ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1)) :=
      Nat.mul_le_mul h3 (Nat.mul_le_mul (Nat.sub_le_sub_right h2 1) (Nat.sub_le_sub_right h3 1))

theorem psu3_ge_of_five_le {q : ℕ} (hq : 5 ≤ q) :
    372000 ≤ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 + 1)) := by
  have h2 : 5 ^ 2 ≤ q ^ 2 := Nat.pow_le_pow_left hq 2
  have h3 : 5 ^ 3 ≤ q ^ 3 := Nat.pow_le_pow_left hq 3
  calc 372000 ≤ 5 ^ 3 * ((5 ^ 2 - 1) * (5 ^ 3 + 1)) := by norm_num
    _ ≤ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 + 1)) :=
      Nat.mul_le_mul h3 (Nat.mul_le_mul (Nat.sub_le_sub_right h2 1) (Nat.add_le_add_right h3 1))

theorem psl3_not_small {q : ℕ} (hq : 2 ≤ q) :
    ¬ (q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1)) = 60 ∨ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1)) = 360 ∨
      q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1)) = 20160 ∨
      q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1)) = 25920) := by
  by_cases h5 : 5 ≤ q
  · have := psl3_ge_of_five_le h5
    omega
  · interval_cases q <;> norm_num

theorem psu3_not_small {q : ℕ} (hq : 2 ≤ q) :
    ¬ (q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 + 1)) = 60 ∨ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 + 1)) = 360 ∨
      q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 + 1)) = 20160 ∨
      q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 + 1)) = 25920) := by
  by_cases h5 : 5 ≤ q
  · have := psu3_ge_of_five_le h5
    omega
  · interval_cases q <;> norm_num

theorem order_ge_of_five_le {q c : ℕ} (hq : 5 ≤ q) (hc : c = q ^ 3 - 1 ∨ c = q ^ 3 + 1) :
    372000 ≤ q ^ 3 * ((q ^ 2 - 1) * c) := by
  rcases hc with rfl | rfl
  · exact psl3_ge_of_five_le hq
  · exact psu3_ge_of_five_le hq

theorem order_not_small {q c : ℕ} (hq : 2 ≤ q) (hc : c = q ^ 3 - 1 ∨ c = q ^ 3 + 1) :
    ¬ (q ^ 3 * ((q ^ 2 - 1) * c) = 60 ∨ q ^ 3 * ((q ^ 2 - 1) * c) = 360 ∨
      q ^ 3 * ((q ^ 2 - 1) * c) = 20160 ∨ q ^ 3 * ((q ^ 2 - 1) * c) = 25920) := by
  rcases hc with rfl | rfl
  · exact psl3_not_small hq
  · exact psu3_not_small hq

theorem lieOrderFormula_small_le {d : TauCeti.ValidLieTypeIndex}
    (h : (∃ q : TauCeti.PrimePower, q.card = 7 ∧ d.1 = .A 1 q) ∨
      (∃ q : TauCeti.PrimePower, q.card = 3 ∧ d.1 = .twistedA 2 q)) :
    CFSG.HardMathSupport.Solomon.Coordinator.I1420.lieOrderFormula d.1 ≤ 20160 := by
  rcases h with ⟨q, hq, hd⟩ | ⟨q, hq, hd⟩
  · rw [hd]
    simp only [CFSG.HardMathSupport.Solomon.Coordinator.I1420.lieOrderFormula, hq]
    norm_num [CFSG.Open.orderA]
  · rw [hd]
    simp only [CFSG.HardMathSupport.Solomon.Coordinator.I1420.lieOrderFormula, hq]
    norm_num [CFSG.Open.orderTwistedA, Finset.prod_Icc_succ_top]

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82
