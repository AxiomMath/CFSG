module

public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.ASVolI.H16

private lemma order_dvd_sixteen {o k : ℕ} (h1 : o ∣ 2 ^ k) (h2 : o ∣ 720) : o ∣ 16 := by
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h1
  rw [hj] at h2 ⊢
  have hcop : Nat.Coprime (2 ^ j) 45 := by
    rcases Nat.eq_zero_or_pos j with hj0 | hjpos
    · subst hj0; decide
    · exact (Nat.coprime_pow_left_iff hjpos 2 45).mpr (by decide)
  have h720 : 2 ^ j ∣ 2 ^ 4 * 45 := by
    rw [show (2 : ℕ) ^ 4 * 45 = 720 by norm_num]
    exact h2
  have hdj : 2 ^ j ∣ 2 ^ 4 := hcop.dvd_of_dvd_mul_right h720
  rw [show (16 : ℕ) = 2 ^ 4 by norm_num]
  exact hdj

private lemma two_pow_pow_eq_one {x : Equiv.Perm (Fin 6)}
    (h : ∃ k : ℕ, x ^ 2 ^ k = 1) : x ^ 16 = 1 := by
  obtain ⟨k, hk⟩ := h
  have h1 : orderOf x ∣ 2 ^ k := orderOf_dvd_iff_pow_eq_one.mpr hk
  have h2 : orderOf x ∣ 720 := by
    have hcard := orderOf_dvd_card (G := Equiv.Perm (Fin 6)) (x := x)
    rw [Fintype.card_perm, Fintype.card_fin,
      show Nat.factorial 6 = 720 from by decide] at hcard
    exact hcard
  exact orderOf_dvd_iff_pow_eq_one.mp (order_dvd_sixteen h1 h2)

private lemma order_dvd_nine {o k : ℕ} (h1 : o ∣ 3 ^ k) (h2 : o ∣ 720) : o ∣ 9 := by
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp h1
  rw [hj] at h2 ⊢
  have hcop : Nat.Coprime (3 ^ j) 80 := by
    rcases Nat.eq_zero_or_pos j with hj0 | hjpos
    · subst hj0; decide
    · exact (Nat.coprime_pow_left_iff hjpos 3 80).mpr (by decide)
  have h720 : 3 ^ j ∣ 3 ^ 2 * 80 := by
    rw [show (3 : ℕ) ^ 2 * 80 = 720 by norm_num]
    exact h2
  have hdj : 3 ^ j ∣ 3 ^ 2 := hcop.dvd_of_dvd_mul_right h720
  rw [show (9 : ℕ) = 3 ^ 2 by norm_num]
  exact hdj

private lemma three_pow_pow_eq_one {x : Equiv.Perm (Fin 6)}
    (h : ∃ k : ℕ, x ^ 3 ^ k = 1) : x ^ 9 = 1 := by
  obtain ⟨k, hk⟩ := h
  have h1 : orderOf x ∣ 3 ^ k := orderOf_dvd_iff_pow_eq_one.mpr hk
  have h2 : orderOf x ∣ 720 := by
    have hcard := orderOf_dvd_card (G := Equiv.Perm (Fin 6)) (x := x)
    rw [Fintype.card_perm, Fintype.card_fin,
      show Nat.factorial 6 = 720 from by decide] at hcard
    exact hcard
  exact orderOf_dvd_iff_pow_eq_one.mp (order_dvd_nine h1 h2)

private theorem comm_exists_order_three :
    ∀ x : Equiv.Perm (Fin 6), x ≠ 1 → x ^ 16 = 1 →
      ∃ g : Equiv.Perm (Fin 6),
        (x * g * x⁻¹ * g⁻¹) ^ 3 = 1 ∧ x * g * x⁻¹ * g⁻¹ ≠ 1 := by
  decide +kernel

private theorem comm_exists_order_five :
    ∀ x : Equiv.Perm (Fin 6), x ≠ 1 → x ^ 9 = 1 →
      ∃ g : Equiv.Perm (Fin 6),
        (x * g * x⁻¹ * g⁻¹) ^ 5 = 1 ∧ x * g * x⁻¹ * g⁻¹ ≠ 1 := by
  decide +kernel

theorem S6_normal_two_group (N : Subgroup (Equiv.Perm (Fin 6))) [N.Normal]
    (h : ∀ x ∈ N, ∃ k : ℕ, x ^ 2 ^ k = 1) : N = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro x hxN
  by_contra hx1
  have hx16 : x ^ 16 = 1 := two_pow_pow_eq_one (h x hxN)
  obtain ⟨g, hg3, hgne⟩ := comm_exists_order_three x hx1 hx16
  have hcN : x * g * x⁻¹ * g⁻¹ ∈ N := by
    have hconj : g * x⁻¹ * g⁻¹ ∈ N :=
      (inferInstance : N.Normal).conj_mem x⁻¹ (inv_mem hxN) g
    simpa only [mul_assoc] using mul_mem hxN hconj
  obtain ⟨k, hk⟩ := h (x * g * x⁻¹ * g⁻¹) hcN
  have hdiv : orderOf (x * g * x⁻¹ * g⁻¹) ∣ 2 ^ k :=
    orderOf_dvd_iff_pow_eq_one.mpr hk
  have hdiv3 : orderOf (x * g * x⁻¹ * g⁻¹) ∣ 3 :=
    orderOf_dvd_iff_pow_eq_one.mpr hg3
  have hgcd : Nat.gcd (2 ^ k) 3 = 1 := by
    rcases Nat.eq_zero_or_pos k with hk0 | hkpos
    · subst hk0; decide
    · exact (Nat.coprime_pow_left_iff hkpos 2 3).mpr (by decide)
  have hone : orderOf (x * g * x⁻¹ * g⁻¹) = 1 := by
    have hdvd := Nat.dvd_gcd hdiv hdiv3
    rw [hgcd] at hdvd
    exact Nat.dvd_one.mp hdvd
  exact hgne (orderOf_eq_one_iff.mp hone)

theorem S6_normal_three_group (N : Subgroup (Equiv.Perm (Fin 6))) [N.Normal]
    (h : ∀ x ∈ N, ∃ k : ℕ, x ^ 3 ^ k = 1) : N = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro x hxN
  by_contra hx1
  have hx9 : x ^ 9 = 1 := three_pow_pow_eq_one (h x hxN)
  obtain ⟨g, hg5, hgne⟩ := comm_exists_order_five x hx1 hx9
  have hcN : x * g * x⁻¹ * g⁻¹ ∈ N := by
    have hconj : g * x⁻¹ * g⁻¹ ∈ N :=
      (inferInstance : N.Normal).conj_mem x⁻¹ (inv_mem hxN) g
    simpa only [mul_assoc] using mul_mem hxN hconj
  obtain ⟨k, hk⟩ := h (x * g * x⁻¹ * g⁻¹) hcN
  have hdiv : orderOf (x * g * x⁻¹ * g⁻¹) ∣ 3 ^ k :=
    orderOf_dvd_iff_pow_eq_one.mpr hk
  have hdiv5 : orderOf (x * g * x⁻¹ * g⁻¹) ∣ 5 :=
    orderOf_dvd_iff_pow_eq_one.mpr hg5
  have hgcd : Nat.gcd (3 ^ k) 5 = 1 := by
    rcases Nat.eq_zero_or_pos k with hk0 | hkpos
    · subst hk0; decide
    · exact (Nat.coprime_pow_left_iff hkpos 3 5).mpr (by decide)
  have hone : orderOf (x * g * x⁻¹ * g⁻¹) = 1 := by
    have hdvd := Nat.dvd_gcd hdiv hdiv5
    rw [hgcd] at hdvd
    exact Nat.dvd_one.mp hdvd
  exact hgne (orderOf_eq_one_iff.mp hone)

end CFSG.ASVolI.H16
