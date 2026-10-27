module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagElation

public section

namespace CFSG.Quasithin.H13.QRC

open Subgroup

section CyclicAction

variable {U : Type*} [AddCommGroup U] [Module (ZMod 2) U]

theorem one_apply_two (v : U) : (1 : U ≃ₗ[ZMod 2] U) v = v := rfl

theorem pow_apply_eq_self {f : U ≃ₗ[ZMod 2] U} {w : U} (h : f w = w) (n : ℕ) :
    (f ^ n) w = w := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, LinearEquiv.mul_apply, h, ih]

theorem zpow_apply_eq_self {f : U ≃ₗ[ZMod 2] U} {w : U} (h : f w = w) (n : ℤ) :
    (f ^ n) w = w := by
  have h' : f⁻¹ w = w := by
    calc f⁻¹ w = f⁻¹ (f w) := by rw [h]
      _ = w := by rw [← LinearEquiv.mul_apply, inv_mul_cancel, one_apply_two]
  induction n using Int.induction_on with
  | zero => simp
  | succ n ih => rw [zpow_add_one, LinearEquiv.mul_apply, h, ih]
  | pred n ih => rw [zpow_sub_one, LinearEquiv.mul_apply, h', ih]

theorem apply_eq_self_of_pow {y : U ≃ₗ[ZMod 2] U} {p m : ℕ} (hp : p.Prime) (hyp : y ^ p = 1)
    (hpm : ¬ p ∣ m) {w : U} (hw : (y ^ m) w = w) : y w = w := by
  have hcop : Nat.gcd m p = 1 := Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp).2 hpm)
  have hbez := Nat.gcd_eq_gcd_ab m p
  rw [hcop] at hbez
  have h1 : y = (y ^ m) ^ (Nat.gcdA m p) * (y ^ p) ^ (Nat.gcdB m p) := by
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, ← zpow_add, ← hbez]
    simp
  rw [hyp, one_zpow, mul_one] at h1
  rw [h1]
  exact zpow_apply_eq_self hw _

theorem mem_range_sub_of_commute {y g : U ≃ₗ[ZMod 2] U} (hgy : g * y = y * g) {w : U}
    (hw : w ∈ LinearMap.range ((y : U →ₗ[ZMod 2] U) - LinearMap.id)) :
    g w ∈ LinearMap.range ((y : U →ₗ[ZMod 2] U) - LinearMap.id) := by
  obtain ⟨u, rfl⟩ := hw
  refine ⟨g u, ?_⟩
  have h := congrArg (fun f : U ≃ₗ[ZMod 2] U => f u) hgy
  simp only [LinearEquiv.mul_apply] at h
  simp [h]

theorem add_self_eq_zero_two (v : U) : v + v = 0 := by
  rw [← two_smul (ZMod 2), show (2 : ZMod 2) = 0 from rfl, zero_smul]

theorem neg_eq_self_two (v : U) : -v = v := by
  rw [neg_eq_iff_add_eq_zero, add_self_eq_zero_two]

theorem eq_zero_of_mem_range_sub_of_fixed {y : U ≃ₗ[ZMod 2] U} (hy : Odd (orderOf y)) {w : U}
    (hw : w ∈ LinearMap.range ((y : U →ₗ[ZMod 2] U) - LinearMap.id)) (hfix : y w = w) :
    w = 0 := by
  obtain ⟨u, rfl⟩ := hw
  simp only [LinearMap.sub_apply, LinearEquiv.coe_coe, LinearMap.id_apply, map_sub] at hfix ⊢
  have h2 : (y * y) u = u := by
    rw [LinearEquiv.mul_apply]
    have h3 : y (y u) = y u - u + y u := by
      have := congrArg (· + y u) hfix
      simpa using this
    rw [h3]
    calc y u - u + y u = (y u + y u) + -u := by abel
      _ = u := by rw [add_self_eq_zero_two, zero_add, neg_eq_self_two]
  obtain ⟨n, hn⟩ := hy
  have hpow : (y * y) ^ (n + 1) = y := by
    rw [← sq, ← pow_mul, show 2 * (n + 1) = orderOf y + 1 by omega, pow_succ,
      pow_orderOf_eq_one, one_mul]
  have h6 := pow_apply_eq_self h2 (n + 1)
  rw [hpow] at h6
  rw [h6, sub_self]

variable [Finite U]

end CyclicAction

section TwoParts

theorem le_of_two_pow_dvd {e k m : ℕ} (hm : Odd m) (h : 2 ^ e ∣ 2 ^ k * m) : e ≤ k := by
  have hcop : Nat.Coprime (2 ^ e) m := Nat.Coprime.pow_left e (Nat.coprime_two_left.2 hm)
  exact (Nat.pow_dvd_pow_iff_le_right (by norm_num)).1 (hcop.dvd_of_dvd_mul_right h)

end TwoParts

open CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial.LinearFlag

end CFSG.Quasithin.H13.QRC
