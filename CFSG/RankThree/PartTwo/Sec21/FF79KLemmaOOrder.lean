module

public import CFSG.HardMathSupport.Solomon.Coordinator.I14_20LieOrd

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF79

open CFSG.Open CFSG.HardMathSupport.Solomon.Coordinator.I1420 Finset

section Aux

private theorem pos_of_not_dvd {q : ℕ} (hq : ¬ 3 ∣ q) : 1 ≤ q := by
  rcases Nat.eq_zero_or_pos q with h | h
  · exact absurd (h ▸ dvd_zero 3) hq
  · exact h

private theorem three_dvd_sq_sub {q : ℕ} (hq : ¬ 3 ∣ q) : 3 ∣ q ^ 2 - 1 := by
  have h1 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ (pos_of_not_dvd hq)
  refine (Nat.modEq_iff_dvd' h1).mp ?_
  have key : ∀ a < 3, ¬ 3 ∣ a → a ^ 2 % 3 = 1 := by decide
  have := key (q % 3) (Nat.mod_lt _ (by norm_num)) (by omega)
  unfold Nat.ModEq
  rw [Nat.pow_mod, this]

end Aux

section Orders

variable {q : ℕ}

private theorem two_pow_mod_three (m : ℕ) : 2 ^ (2 * m + 1) % 3 = 2 := by
  induction m with
  | zero => norm_num
  | succ n ih =>
    have : 2 ^ (2 * (n + 1) + 1) = 4 * 2 ^ (2 * n + 1) := by ring
    omega

end Orders

theorem not_three_dvd_lieOrderFormula_suzuki (m : ℕ) :
    ¬ 3 ∣ lieOrderFormula (TauCeti.LieTypeIndex.suzuki m) := by
  have hm := two_pow_mod_three m
  show ¬ 3 ∣ orderSuzuki (2 ^ (2 * m + 1))
  unfold orderSuzuki
  generalize 2 ^ (2 * m + 1) = q at hm ⊢
  have hq : ¬ 3 ∣ q := by omega
  have h2 := three_dvd_sq_sub hq
  have h1 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ (pos_of_not_dvd hq)
  intro h
  rcases (Nat.Prime.dvd_mul Nat.prime_three).1 h with h | h
  · rcases (Nat.Prime.dvd_mul Nat.prime_three).1 h with h | h
    · exact hq (Nat.prime_three.dvd_of_dvd_pow h)
    · omega
  · omega

end CFSG.RankThree.PartTwo.Sec21.FF79
