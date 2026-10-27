module

public import CFSG.Timmesfeld.Moufang.Criterion

public section

namespace CFSG.Timmesfeld.Closure

open CFSG.Timmesfeld.Moufang

variable {G : Type*} [Group G] {D : Set G}

theorem commute_conj_of_orderOf_eq_four {a b : G} (ha : a * a = 1) (hb : b * b = 1)
    (h4 : orderOf (a * b) = 4) : Commute a (b * a * b) := by
  have hpow : (a * b) ^ 4 = 1 := by rw [← h4]; exact pow_orderOf_eq_one _
  have hab : (a * (b * a * b)) * (a * (b * a * b)) = 1 := by
    calc (a * (b * a * b)) * (a * (b * a * b)) = (a * b) ^ 4 := by
          rw [show (4 : ℕ) = 1 + 1 + 1 + 1 from rfl, pow_succ, pow_succ, pow_succ, pow_one]
          group
      _ = 1 := hpow
  have hbab : (b * a * b) * (b * a * b) = 1 := by
    calc (b * a * b) * (b * a * b) = b * a * (b * b) * a * b := by group
      _ = 1 := by rw [hb, mul_one, show b * a * a * b = b * (a * a) * b by group, ha, mul_one, hb]
  have hainv : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  have hxinv : (b * a * b)⁻¹ = b * a * b := inv_eq_of_mul_eq_one_right hbab
  have hprodinv : (a * (b * a * b))⁻¹ = a * (b * a * b) := inv_eq_of_mul_eq_one_right hab
  show a * (b * a * b) = (b * a * b) * a
  calc a * (b * a * b) = (a * (b * a * b))⁻¹ := hprodinv.symm
    _ = (b * a * b)⁻¹ * a⁻¹ := mul_inv_rev _ _
    _ = (b * a * b) * a := by rw [hxinv, hainv]

theorem not_special_special_of_opposite (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g})
    (hD : IsRootInvolutionSet D) {u v c : G} (hu : u ∈ D) (hv : v ∈ D) (huv : Commute u v)
    (hc : c ∈ D) (huc : ¬ Commute u c) (hodd : Odd (orderOf (u * c)))
    (h1 : orderOf (c * v) = 4) (h2 : orderOf (c * (u * v)) = 4) : False := by
  have hu2 : u * u = 1 := hD.mul_self_eq_one hu
  have hv2 : v * v = 1 := hD.mul_self_eq_one hv
  have hc2 : c * c = 1 := hD.mul_self_eq_one hc
  have huv2 : (u * v) * (u * v) = 1 := by
    calc (u * v) * (u * v) = u * (v * u) * v := by group
      _ = u * (u * v) * v := by rw [huv.eq]
      _ = 1 := by rw [show u * (u * v) * v = (u * u) * (v * v) by group, hu2, hv2, one_mul]
  have hvinv : v⁻¹ = v := inv_eq_of_mul_eq_one_right hv2
  have huvinv : (u * v)⁻¹ = u * v := inv_eq_of_mul_eq_one_right huv2
  set x := v * c * v with hx
  set y := (u * v) * c * (u * v) with hy
  have hxD : x ∈ D := by
    have := conj_mem_of_isClass hclass v hc
    rwa [hvinv] at this
  have hyD : y ∈ D := by
    have := conj_mem_of_isClass hclass (u * v) hc
    rwa [huvinv] at this
  have hcx : Commute c x := commute_conj_of_orderOf_eq_four hc2 hv2 h1
  have hcy : Commute c y := commute_conj_of_orderOf_eq_four hc2 huv2 h2
  have hxcD : x * c ∈ D := by
    have h4 : orderOf (v * c) = 4 := by rwa [orderOf_mul_comm_eq]
    have hsq := hD.2.2 v hv c hc h4
    have : x * c = (v * c) ^ 2 := by rw [hx, pow_two]; group
    rwa [this]
  have hyx : y * x = v * (u * c) ^ 2 * v⁻¹ := by
    rw [hy, hx, hvinv, pow_two]
    calc u * v * c * (u * v) * (v * c * v) = u * v * c * u * (v * v) * c * v := by group
      _ = u * v * c * u * c * v := by rw [hv2, mul_one]
      _ = v * u * c * u * c * v := by rw [← huv.eq]
      _ = v * (u * c * (u * c)) * v := by group
  have hoddyx : Odd (orderOf (y * x)) := by
    rw [hyx, orderOf_conj_eq, orderOf_pow' _ (by norm_num : (2 : ℕ) ≠ 0)]
    exact Odd.of_dvd_nat hodd (Nat.div_dvd_of_dvd (Nat.gcd_dvd_left _ _))
  have hyx1 : y * x = 1 :=
    eq_of_collinear_of_odd hD hc hcx.symm hxcD hyD hcy.symm hoddyx
  have hsq : (u * c) ^ 2 = 1 := by
    have h := hyx1
    rw [hyx] at h
    have : (u * c) ^ 2 = v⁻¹ * (v * (u * c) ^ 2 * v⁻¹) * v := by group
    rw [this, h]
    group
  exact huc ((commute_iff_mul_sq_eq_one hu2 hc2).2 hsq)

end CFSG.Timmesfeld.Closure
