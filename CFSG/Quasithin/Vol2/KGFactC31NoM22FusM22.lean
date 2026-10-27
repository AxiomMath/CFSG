module

public import CFSG.Sporadic.Mathieu.M22

public section

namespace CFSG.Quasithin.KGC31

open CFSG.Blueprint CFSG.Sporadic.Mathieu

theorem m22_facts_eleven :
    orderOf (m22a * m22b : NativeSporadic.M22) = 11 ∧
    (m22b * m22a * m22b * m22a * m22b⁻¹ * m22a * m22b⁻¹ * m22a * m22b⁻¹ * m22a * m22b * m22b *
        m22a * m22b⁻¹ * m22a * m22b * m22a * m22b * m22b * m22a * m22b⁻¹ :
      NativeSporadic.M22) * (m22a * m22b) *
      (m22b * m22a * m22b * m22a * m22b⁻¹ * m22a * m22b⁻¹ * m22a * m22b⁻¹ * m22a * m22b * m22b *
        m22a * m22b⁻¹ * m22a * m22b * m22a * m22b * m22b * m22a * m22b⁻¹)⁻¹ =
      (m22a * m22b) ^ 3 := by
  refine ⟨?_, ?_⟩
  · haveI : Fact (Nat.Prime 11) := ⟨by norm_num⟩
    apply orderOf_eq_prime
    · decide +kernel
    · decide +kernel
  · decide +kernel

theorem m22_facts_five :
    orderOf (m22a * m22b * m22b : NativeSporadic.M22) = 5 ∧
    (m22b * m22a * m22b * m22a * m22b * m22a * m22b * m22a * m22b * m22b * m22a * m22b⁻¹ *
        m22a * m22b * m22a * m22b * m22b * m22a * m22b * m22a * m22b⁻¹ * m22a * m22b * m22b *
        m22a * m22b * m22a * m22b * m22a * m22b :
      NativeSporadic.M22) * (m22a * m22b * m22b) *
      (m22b * m22a * m22b * m22a * m22b * m22a * m22b * m22a * m22b * m22b * m22a * m22b⁻¹ *
        m22a * m22b * m22a * m22b * m22b * m22a * m22b * m22a * m22b⁻¹ * m22a * m22b * m22b *
        m22a * m22b * m22a * m22b * m22a * m22b)⁻¹ =
      (m22a * m22b * m22b) ^ 3 := by
  refine ⟨?_, ?_⟩
  · haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    apply orderOf_eq_prime
    · decide +kernel
    · decide +kernel
  · decide +kernel

theorem m22_exists_eleven : ∃ a b : CFSG.Blueprint.NativeSporadic.Carrier .M22,
    orderOf a = 11 ∧ b * a * b⁻¹ = a ^ 3 :=
  ⟨m22a * m22b,
    m22b * m22a * m22b * m22a * m22b⁻¹ * m22a * m22b⁻¹ * m22a * m22b⁻¹ * m22a * m22b * m22b *
      m22a * m22b⁻¹ * m22a * m22b * m22a * m22b * m22b * m22a * m22b⁻¹,
    m22_facts_eleven.1, m22_facts_eleven.2⟩

theorem m22_exists_five : ∃ c d : CFSG.Blueprint.NativeSporadic.Carrier .M22,
    orderOf c = 5 ∧ d * c * d⁻¹ = c ^ 3 :=
  ⟨m22a * m22b * m22b,
    m22b * m22a * m22b * m22a * m22b * m22a * m22b * m22a * m22b * m22b * m22a * m22b⁻¹ *
      m22a * m22b * m22a * m22b * m22b * m22a * m22b * m22a * m22b⁻¹ * m22a * m22b * m22b *
      m22a * m22b * m22a * m22b * m22a * m22b,
    m22_facts_five.1, m22_facts_five.2⟩

theorem five_dvd_of_three_pow_modEq_eleven {m : ℕ} (h : 3 ^ m ≡ 1 [MOD 11]) : 5 ∣ m := by
  have h1 : (3 : ZMod 11) ^ m = 1 := by
    have := (ZMod.natCast_eq_natCast_iff _ _ _).2 h
    push_cast at this
    exact this
  have h5 : orderOf (3 : ZMod 11) = 5 := by
    haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    apply orderOf_eq_prime
    · decide
    · decide
  rw [← h5]
  exact orderOf_dvd_of_pow_eq_one h1

theorem four_dvd_of_three_pow_modEq_five {m : ℕ} (h : 3 ^ m ≡ 1 [MOD 5]) : 4 ∣ m := by
  have h1 : (3 : ZMod 5) ^ m = 1 := by
    have := (ZMod.natCast_eq_natCast_iff _ _ _).2 h
    push_cast at this
    exact this
  have h4 : orderOf (3 : ZMod 5) = 4 := by
    rw [orderOf_eq_iff (by norm_num)]
    decide
  rw [← h4]
  exact orderOf_dvd_of_pow_eq_one h1

end CFSG.Quasithin.KGC31

end
