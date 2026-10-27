module

public import CFSG.Blueprint.Catalog
public import CFSG.Open.SplitBNPair
import CFSG.Quasithin.Vol2.Ch5Sec1L34Lem516
import CFSG.NumberTheory.TwoPowAddOneOdd
import CFSG.Milestones.ASVolI.I2

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.KFourteenSixNBar

open CFSG.Blueprint

variable {X : Type} [Group X] [Finite X]

omit [Finite X] in
theorem not_dvd_card_of_suzukiModel {f r : ℕ}
    (hX : SuzukiModel X 2 f) (hr : r.Prime) (hr3 : 3 < r)
    (hn : ∃ n : ℕ, Odd n ∧ r ∣ 2 ^ n + 1) : ¬ r ∣ Nat.card X := by
  obtain ⟨n, hn, hrn⟩ := hn
  obtain ⟨a, -, rfl, hcard⟩ := CFSG.Quasithin.H13.card_of_suzukiModel hX
  have hr2 : r ≠ 2 := by omega
  rw [hcard]
  intro h
  rcases (Nat.Prime.dvd_mul hr).1 h with h | h
  · rcases (Nat.Prime.dvd_mul hr).1 h with h | h
    · exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1
        (hr.dvd_of_dvd_pow (hr.dvd_of_dvd_pow h)))
    · exact CFSG.NumberTheory.not_dvd_two_pow_sub_one_of_dvd_two_pow_add_one hr hr2 hrn
        (odd_two_mul_add_one a) h
  · rw [← pow_mul] at h
    exact CFSG.NumberTheory.not_dvd_two_pow_add_one_of_even hr hr2 hn hrn
      (Nat.even_mul.2 (Or.inr even_two)) h

theorem exists_splitBNPair_of_suzukiModel {L : Type} [Group L]
    [Finite L] {f : ℕ} (hL : SuzukiModel L 2 f) :
    2 ∣ Nat.card L ∧ ∃ B N : Subgroup L, CFSG.ASVolI.ChIJK.IsSplitBNPair 2 B N := by
  refine ⟨?_, CFSG.ASVolI.ChIJK.burnsideI2BN_suzuki_model hL⟩
  obtain ⟨a, -, rfl, hcard⟩ := CFSG.Quasithin.H13.card_of_suzukiModel hL
  rw [hcard]
  exact ((dvd_pow (dvd_pow_self 2 (by omega)) two_ne_zero).mul_right _).mul_right _

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.KFourteenSixNBar
