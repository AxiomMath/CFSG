module

public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.Quasithin.H13

theorem centralizes_of_quot_cs5 {G : Type} [Group G] {P U : Subgroup G} (hU2 : IsPGroup 2 U)
    {x : G} (hxo : Odd (orderOf x)) (hxU : ∀ u ∈ U, x * u = u * x)
    (hxPU : ∀ p ∈ P, x * p * x⁻¹ * p⁻¹ ∈ U) : ∀ p ∈ P, x * p = p * x := by
  intro p hp
  obtain ⟨u, hu⟩ : ∃ u : G, u = x * p * x⁻¹ * p⁻¹ := ⟨_, rfl⟩
  have huU : u ∈ U := by
    rw [hu]
    exact hxPU p hp
  have hxu : Commute x u := hxU u huU
  have hxp : x * p = u * p * x := by
    rw [hu]
    group
  have hconj : ∀ k : ℕ, x ^ k * p = u ^ k * p * x ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      calc x ^ (k + 1) * p = x * (x ^ k * p) := by rw [pow_succ' x k, mul_assoc]
        _ = x * (u ^ k * p * x ^ k) := by rw [ih]
        _ = (x * u ^ k) * p * x ^ k := by simp only [mul_assoc]
        _ = (u ^ k * x) * p * x ^ k := by rw [(hxu.pow_right k).eq]
        _ = u ^ k * (x * p) * x ^ k := by simp only [mul_assoc]
        _ = u ^ k * (u * p * x) * x ^ k := by rw [hxp]
        _ = u ^ (k + 1) * p * x ^ (k + 1) := by
          rw [pow_succ u k, pow_succ' x k]
          simp only [mul_assoc]
  have hum : u ^ orderOf x = 1 := by
    have h1 := hconj (orderOf x)
    simp only [pow_orderOf_eq_one, one_mul, mul_one] at h1
    have h2 : u ^ orderOf x * p = 1 * p := by
      rw [one_mul]
      exact h1.symm
    exact mul_right_cancel h2
  have hu1 : u = 1 := by
    obtain ⟨j, hj⟩ := hU2 ⟨u, huU⟩
    have hj' : u ^ 2 ^ j = 1 := by simpa using congrArg Subtype.val hj
    have hd1 : orderOf u ∣ 2 ^ j := orderOf_dvd_of_pow_eq_one hj'
    have hd2 : orderOf u ∣ orderOf x := orderOf_dvd_of_pow_eq_one hum
    have hcop : Nat.Coprime (2 ^ j) (orderOf x) :=
      Nat.Coprime.pow_left j (Nat.Coprime.symm (Odd.coprime_two_right hxo))
    have hcop' : Nat.Coprime (orderOf u) (orderOf x) := Nat.Coprime.coprime_dvd_left hd1 hcop
    exact orderOf_eq_one_iff.mp (hcop'.eq_one_of_dvd hd2)
  calc x * p = (x * p * x⁻¹ * p⁻¹) * (p * x) := by group
    _ = u * (p * x) := by rw [hu]
    _ = p * x := by rw [hu1, one_mul]

theorem exists_five_power_lift_cs5 {A B : Type} [Group A] [Group B] [Finite A] (f : A →* B)
    {c : B} (hc : c ∈ f.range) (hc1 : c ≠ 1) {k : ℕ} (hck : c ^ 5 ^ k = 1) :
    ∃ x : A, f x ≠ 1 ∧ ∃ a : ℕ, x ^ 5 ^ a = 1 ∧ ∃ m : ℕ, f x = c ^ m := by
  obtain ⟨x₀, rfl⟩ := MonoidHom.mem_range.mp hc
  obtain ⟨a, m, hm, hdec⟩ :=
    Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos x₀).ne' 5 (by norm_num)
  have hcop : Nat.Coprime m (5 ^ k) :=
    Nat.Coprime.pow_right k (Nat.Coprime.symm ((Nat.prime_five.coprime_iff_not_dvd).mpr hm))
  refine ⟨x₀ ^ m, ?_, a, ?_, m, ?_⟩
  · intro h1
    rw [map_pow] at h1
    have h2 : f x₀ ^ Nat.gcd m (5 ^ k) = 1 := pow_gcd_eq_one.mpr ⟨h1, hck⟩
    have hg : Nat.gcd m (5 ^ k) = 1 := hcop
    rw [hg, pow_one] at h2
    exact hc1 h2
  · have e : m * 5 ^ a = orderOf x₀ := by
      rw [hdec, mul_comm]
    rw [← pow_mul, e, pow_orderOf_eq_one]
  · rw [map_pow]

end CFSG.Quasithin.H13
