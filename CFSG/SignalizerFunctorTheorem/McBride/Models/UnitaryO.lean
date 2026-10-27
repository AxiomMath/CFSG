module

public import CFSG.SignalizerFunctorTheorem.McBride.Models.AutItems
import CFSG.SignalizerFunctorTheorem.McBride.Models.NearSolvable.Arith
import CFSG.SignalizerFunctorTheorem.McBride.Models.NearSolvable.Orders
import CFSG.SignalizerFunctorTheorem.McBride.Models.Unitary
import CFSG.SignalizerFunctorTheorem.McBride.Models.UnitaryO.Sylow

public section

open CFSG.Open

namespace CFSG.SignalizerFunctorTheorem.McBride

namespace UnitaryO

theorem eq_two_or_three_of_prime_dvd_seventy_two {r : ℕ} (hr : r.Prime) (h : r ∣ 72) :
    r = 2 ∨ r = 3 := by
  have h' : r ∣ 2 ^ 3 * 3 ^ 2 := by norm_num; exact h
  rcases (Nat.Prime.dvd_mul hr).mp h' with h2 | h3
  · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp (hr.dvd_of_dvd_pow h2))
  · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_three).mp (hr.dvd_of_dvd_pow h3))

theorem five_le_of_not_dvd_seventy_two {r : ℕ} (hr : r.Prime) (h : ¬ r ∣ 72) : 5 ≤ r := by
  by_contra hlt
  have h2 := hr.two_le
  interval_cases r
  · exact h (by norm_num)
  · exact h (by norm_num)
  · exact absurd hr (by norm_num)

theorem exists_prime_dvd_card_psu3 {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) :
    ∃ r : ℕ, r.Prime ∧ r ∣ Nat.card (PSU3 2 p) ∧ ¬ r ∣ 72 := by
  have hodd : Odd p := hp.odd_of_ne_two (by omega)
  have h32 : 2 ^ p % 3 = 2 := NearSolvable.two_pow_mod_three hodd
  have h2p : 2 ^ 5 ≤ 2 ^ p := Nat.pow_le_pow_right (by norm_num) h5
  have heven : 2 ^ p % 2 = 0 := Nat.even_iff.mp (Nat.even_pow.mpr ⟨even_two, hp.ne_zero⟩)
  obtain ⟨r, hr, hrd⟩ := Nat.exists_prime_and_dvd (show 2 ^ p - 1 ≠ 1 by omega)
  have hr2 : r ≠ 2 := by
    rintro rfl
    omega
  have hr3 : r ≠ 3 := by
    rintro rfl
    omega
  refine ⟨r, hr, ?_, fun h => ?_⟩
  · have hmul := NearSolvable.card_psu3_mul_gcd hp.one_le
    have h3 : Nat.gcd 3 (2 ^ p + 1) = 3 := Nat.gcd_eq_left (by omega)
    rw [h3] at hmul
    have hdvd : r ∣ Nat.card (PSU3 2 p) * 3 := by
      rw [hmul]
      refine Dvd.dvd.mul_left (Dvd.dvd.mul_right ?_ _) _
      rw [show (2 ^ p) ^ 2 - 1 = (2 ^ p + 1) * (2 ^ p - 1) by rw [← Nat.sq_sub_sq, one_pow]]
      exact hrd.mul_left _
    rcases (Nat.Prime.dvd_mul hr).mp hdvd with h | h
    · exact h
    · exact absurd ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_three).mp h) hr3
  · rcases eq_two_or_three_of_prime_dvd_seventy_two hr h with h | h
    · exact hr2 h
    · exact hr3 h

end UnitaryO

open UnitaryO

theorem itemO_psu3 {p : ℕ} (hp : p.Prime) (hcop : Nat.Coprime p (Nat.card (PSU3 2 p)))
    (_hnear : signalizerNearPSolvable p (PSU3 2 p)) (f : MulAut (PSU3 2 p))
    (hf : orderOf f = p) : ItemO f := by
  have h5 := UnitaryFrame.five_le_of_coprime hp hcop
  have hM : Nat.card (fixedNormalizer f) = 72 := by
    rw [fixedNormalizer_psu3 hp hcop f hf]
    exact UnitaryFrame.card_fixedSubgroup hp hcop f hf
  rw [ItemO, hM]
  obtain ⟨r, hr, hrY, hr72⟩ := exists_prime_dvd_card_psu3 hp h5
  exact ⟨⟨r, hr, hrY, hr72⟩, fun r hr _ hr72 R =>
    isMulCommutative_sylow_psu3 hp hr (five_le_of_not_dvd_seventy_two hr hr72) R⟩

end CFSG.SignalizerFunctorTheorem.McBride
