module

public import CFSG.Timmesfeld.Orders.Bang

public section

namespace CFSG.Timmesfeld

theorem exists_prime_dvd_two_pow_sub_one_not_dvd_two_mul {m : ℕ} (hm : 2 ≤ m) :
    ∃ r : ℕ, r.Prime ∧ r ∣ 2 ^ m - 1 ∧ ¬ r ∣ 2 * m := by
  by_cases hm6 : m = 6
  · subst hm6
    exact ⟨7, by norm_num, by norm_num, by norm_num⟩
  · obtain ⟨r, hr, hrm, hprim⟩ :=
      exists_primitive_prime_dvd_two_pow_sub_one m hm hm6
    have hpp : IsPrimitivePrimeDivisor r m := ⟨hr, hrm, hprim⟩
    refine ⟨r, hr, hrm, ?_⟩
    have hr2 : r ≠ 2 := hpp.ne_two (by omega)
    have hmr : m ∣ r - 1 := by
      have hr1 : r ∣ 2 ^ (r - 1) - 1 := by
        have hcop : ¬ r ∣ 2 := fun hd =>
          hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1 hd)
        have h := Nat.ModEq.pow_totient
          (Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hr).2 hcop))
        rw [Nat.totient_prime hr] at h
        exact (Nat.modEq_iff_dvd' (Nat.one_le_two_pow)).1 h.symm
      exact (hpp.dvd_sub_one_iff (by omega) (r - 1)).1 hr1
    have hpos : 0 < r - 1 := by have := hr.two_le; omega
    have hmr' : m < r := by
      have := Nat.le_of_dvd hpos hmr
      omega
    intro hdiv
    rcases hr.dvd_mul.mp hdiv with h2 | hmdiv
    · exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1 h2)
    · have := Nat.le_of_dvd (by omega) hmdiv
      omega

end CFSG.Timmesfeld
