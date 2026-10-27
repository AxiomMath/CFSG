module

public import Mathlib.Data.Nat.Prime.Defs

import CFSG.Timmesfeld.Orders.Bang

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Timmesfeld

theorem exists_lemmaW_primePow {k m : ℕ} (hk : 2 ≤ k) (hm : 0 < m) (hmk : m < 2 * k) :
    ∃ p a : ℕ, p.Prime ∧ p ≠ 2 ∧ p ^ a ∣ 2 ^ k + 1 ∧
      Nat.gcd (p ^ a) m * Nat.gcd (p ^ a) (2 ^ m - 1) < p ^ a := by
  by_cases hk3 : k = 3
  · subst hk3
    have hm6 : m < 6 := by omega
    refine ⟨3, 2, Nat.prime_three, by decide, by decide, ?_⟩
    interval_cases m <;> decide
  · obtain ⟨p, hp, hpdvd, hprim⟩ :=
      exists_primitive_prime_dvd_two_pow_sub_one (2 * k) (by omega)
        (by omega : 2 * k ≠ 6)
    have hpp : IsPrimitivePrimeDivisor p (2 * k) := ⟨hp, hpdvd, hprim⟩
    have hp2 : p ≠ 2 := hpp.ne_two (by omega)
    have hpadd : p ∣ 2 ^ k + 1 := by
      refine (hpp.dvd_add_one_iff (by omega) k).mpr ⟨dvd_rfl, ?_⟩
      intro hkdvd
      have := Nat.le_of_dvd (by omega) hkdvd
      omega
    have hpgt : 2 * k < p := by
      have hcop : Nat.Coprime 2 p :=
        (Nat.coprime_primes Nat.prime_two hp).mpr hp2.symm
      have hfermat : 2 ^ (p - 1) ≡ 1 [MOD p] := Nat.ModEq.pow_card_sub_one_eq_one hp hcop
      have hdvd : p ∣ 2 ^ (p - 1) - 1 :=
        (Nat.modEq_iff_dvd' Nat.one_le_two_pow).mp hfermat.symm
      have hindex : 2 * k ∣ p - 1 := (hpp.dvd_sub_one_iff (by omega) (p - 1)).mp hdvd
      have hle : 2 * k ≤ p - 1 := Nat.le_of_dvd (by have := hp.two_le; omega) hindex
      have := hp.two_le
      omega
    have hgm : Nat.gcd p m = 1 := by
      rw [← Nat.coprime_iff_gcd_eq_one]
      refine (hp.coprime_iff_not_dvd).mpr ?_
      intro hdvd
      have := Nat.le_of_dvd hm hdvd
      omega
    have hg2 : Nat.gcd p (2 ^ m - 1) = 1 := by
      rw [← Nat.coprime_iff_gcd_eq_one]
      refine (hp.coprime_iff_not_dvd).mpr ?_
      intro hdvd
      have hindex : 2 * k ∣ m := (hpp.dvd_sub_one_iff (by omega) m).mp hdvd
      have := Nat.le_of_dvd hm hindex
      omega
    refine ⟨p, 1, hp, hp2, by simpa using hpadd, ?_⟩
    rw [pow_one, hgm, hg2, one_mul]
    exact hp.one_lt

end CFSG.Quasithin.Stroth

end
