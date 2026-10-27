module

public import Mathlib.FieldTheory.Finite.Basic

public section

namespace CFSG.Quasithin.F112Crit

namespace NormalPrimeAction

variable {Γ : Type*} [Group Γ] {p : ℕ} {s c : Γ} {k : ℤ}

theorem conj_zpow_eq (hs : s * c * s⁻¹ = c ^ k) (j : ℤ) : s * c ^ j * s⁻¹ = c ^ (k * j) := by
  rw [← conj_zpow, hs, ← zpow_mul]

theorem pow_conj (hs : s * c * s⁻¹ = c ^ k) (n : ℕ) :
    s ^ n * c * (s ^ n)⁻¹ = c ^ (k ^ n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have e : s ^ (n + 1) * c * (s ^ (n + 1))⁻¹ = s * (s ^ n * c * (s ^ n)⁻¹) * s⁻¹ := by
      rw [pow_succ']; group
    rw [e, ih, conj_zpow_eq hs, pow_succ']

theorem zpow_eq_self_of_dvd (hc : orderOf c = p) (h : (p : ℤ) ∣ k - 1) : c ^ k = c := by
  have h1 : c ^ (k - 1) = 1 := orderOf_dvd_iff_zpow_eq_one.mp (by rw [hc]; exact h)
  rw [zpow_sub, zpow_one, mul_inv_eq_one] at h1
  exact h1

theorem zpow_eq_inv_of_dvd (hc : orderOf c = p) (h : (p : ℤ) ∣ k + 1) : c ^ k = c⁻¹ := by
  have h1 : c ^ (k + 1) = 1 := orderOf_dvd_iff_zpow_eq_one.mp (by rw [hc]; exact h)
  rw [zpow_add_one, mul_eq_one_iff_eq_inv] at h1
  exact h1

theorem dvd_sub_one_or_dvd_add_one (hp : p.Prime) (hc : orderOf c = p)
    (hs : s * c * s⁻¹ = c ^ k) (hss : s * s = 1) : (p : ℤ) ∣ k - 1 ∨ (p : ℤ) ∣ k + 1 := by
  have hs' : s⁻¹ = s := inv_eq_of_mul_eq_one_right hss
  have h1 : c = c ^ (k * k) := by
    have e : s * (s * c * s⁻¹) * s⁻¹ = c := by
      calc s * (s * c * s⁻¹) * s⁻¹ = (s * s) * c * (s⁻¹ * s⁻¹) := by group
        _ = c := by rw [← mul_inv_rev, hss, inv_one]; simp
    calc c = s * (s * c * s⁻¹) * s⁻¹ := e.symm
      _ = s * c ^ k * s⁻¹ := by rw [hs]
      _ = (s * c * s⁻¹) ^ k := conj_zpow.symm
      _ = (c ^ k) ^ k := by rw [hs]
      _ = c ^ (k * k) := (zpow_mul c k k).symm
  have h2 : c ^ (k * k - 1) = 1 := by
    rw [zpow_sub, zpow_one, ← h1, mul_inv_cancel]
  have h3 : (p : ℤ) ∣ k * k - 1 := by
    have := orderOf_dvd_iff_zpow_eq_one.mpr h2
    rwa [hc] at this
  have h4 : (p : ℤ) ∣ (k - 1) * (k + 1) := by
    have : (k - 1) * (k + 1) = k * k - 1 := by ring
    rwa [this]
  exact (Nat.prime_iff_prime_int.mp hp).dvd_or_dvd h4

theorem cent_or_inv (hp : p.Prime) (hc : orderOf c = p) (hs : s * c * s⁻¹ = c ^ k)
    (hss : s * s = 1) :
    s * c * s⁻¹ = c ∨ s * c * s⁻¹ = c⁻¹ := by
  rcases dvd_sub_one_or_dvd_add_one hp hc hs hss with h | h
  · left; rw [hs]; exact zpow_eq_self_of_dvd hc h
  · right; rw [hs]; exact zpow_eq_inv_of_dvd hc h

theorem pow_pred_cent (hp : p.Prime) (hc : orderOf c = p) (hs : s * c * s⁻¹ = c ^ k) :
    s ^ (p - 1) * c * (s ^ (p - 1))⁻¹ = c := by
  have hndvd : ¬ (p : ℤ) ∣ k := by
    intro hk
    have h1 : c ^ k = 1 := orderOf_dvd_iff_zpow_eq_one.mp (by rw [hc]; exact hk)
    rw [h1] at hs
    have : c = 1 := by simpa using hs
    rw [this, orderOf_one] at hc
    exact hp.one_lt.ne hc
  have hcop : IsCoprime k (p : ℤ) := by
    have := (Nat.prime_iff_prime_int.mp hp).irreducible.coprime_iff_not_dvd.mpr hndvd
    exact this.symm
  have hferm := Int.ModEq.pow_card_sub_one_eq_one hp hcop
  have h2 : (p : ℤ) ∣ k ^ (p - 1) - 1 := (Int.modEq_iff_dvd.mp hferm.symm)
  rw [pow_conj hs]
  exact zpow_eq_self_of_dvd hc h2

end NormalPrimeAction

end CFSG.Quasithin.F112Crit
