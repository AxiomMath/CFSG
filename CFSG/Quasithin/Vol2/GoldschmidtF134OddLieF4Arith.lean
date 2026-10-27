module

public import CFSG.Quasithin.Vol2.GoldschmidtF134OddSzArith

public section

namespace CFSG.Quasithin.H13.NQCore.F4

theorem three_dvd_two_pow_add_one (a : ℕ) : 3 ∣ 2 ^ (2 * a + 1) + 1 := by
  simpa using Odd.nat_add_dvd_pow_add_pow 2 1 (odd_two_mul_add_one a)

theorem two_pow_add_one_not_dvd_prime_pow {a p b : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    ¬ 2 ^ (2 * a + 1) + 1 ∣ p ^ b := by
  intro h
  have h3 : 3 ∣ p ^ b := (three_dvd_two_pow_add_one a).trans h
  have h3p : 3 = p := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).1
    (Nat.prime_three.dvd_of_dvd_pow h3)
  omega

theorem two_pow_sq_add_one_not_dvd_prime_pow {a p b : ℕ} (hp : p.Prime) (ha : 1 ≤ a) :
    ¬ (2 ^ (2 * a + 1)) ^ 2 + 1 ∣ p ^ b :=
  not_dvd_of_prime_factors hp ha fun _ hr hrd =>
    Or.inr ((Nat.prime_dvd_prime_iff_eq hr hp).1 (hr.dvd_of_dvd_pow hrd))

end CFSG.Quasithin.H13.NQCore.F4
