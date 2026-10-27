module

public import CFSG.Timmesfeld.Bridge.RootStructBasic

public section

namespace CFSG.Timmesfeld.Bridge

open CFSG.Timmesfeld

variable {G : Type*} [Group G] {D : Set G}

namespace RootStructQ

theorem conj_mul_mul (g h x : G) : g * h * x * (g * h)⁻¹ = g * (h * x * h⁻¹) * g⁻¹ := by group

theorem commute_of_conj_eq {g x : G} (h : g * x * g⁻¹ = x) : Commute g x := by
  show g * x = x * g
  calc g * x = g * x * g⁻¹ * g := by group
    _ = x * g := by rw [h]

theorem commute_pow_three_of_cycle {t x₀ x₁ x₂ : G} (h0 : t * x₀ * t⁻¹ = x₁)
    (h1 : t * x₁ * t⁻¹ = x₂) (h2 : t * x₂ * t⁻¹ = x₀) : Commute (t ^ 3) x₀ := by
  apply commute_of_conj_eq
  rw [pow_three]
  calc t * (t * t) * x₀ * (t * (t * t))⁻¹ = t * (t * (t * x₀ * t⁻¹) * t⁻¹) * t⁻¹ := by group
    _ = x₀ := by rw [h0, h1, h2]

theorem conj_conj_of_sq {z x : G} (hz : z * z = 1) : z * (z * x * z⁻¹) * z⁻¹ = x := by
  rw [show z * (z * x * z⁻¹) * z⁻¹ = (z * z) * x * (z * z)⁻¹ by group, hz, one_mul, inv_one,
    mul_one]

theorem conj_pow_mul_left_eq_inv {x y : G} (hx : x * x = 1) (hy : y * y = 1) (n : ℕ) :
    x * (x * y) ^ n * x⁻¹ = ((x * y) ^ n)⁻¹ := by
  have hx' : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx
  have hy' : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy
  rw [← conj_pow, ← inv_pow, mul_inv_rev, hx', hy', ← mul_assoc x x y, hx, one_mul]

theorem conj_pow_mul_right_eq_inv {x y : G} (hx : x * x = 1) (hy : y * y = 1) (n : ℕ) :
    x * (y * x) ^ n * x⁻¹ = ((y * x) ^ n)⁻¹ := by
  have hx' : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx
  have hy' : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy
  rw [← conj_pow, ← inv_pow, mul_inv_rev, hx', hy', mul_assoc x (y * x) x, mul_assoc y x x, hx,
    mul_one]

end RootStructQ

open RootStructQ

theorem commute_pow_three_of_four_group {w z u v : G} (hw : w * w = 1) (hz : z * z = 1)
    (hu : u * u = 1) (huv : Commute u v) (hwu : Commute w u) (hwv : w * v * w = u * v)
    (hzu : z * u * z = v) : Commute ((w * z) ^ 3) u := by
  have hw' : w⁻¹ = w := inv_eq_of_mul_eq_one_right hw
  have hz' : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz
  have cwu : w * u * w⁻¹ = u := by rw [hwu.eq, mul_inv_cancel_right]
  have cwv : w * v * w⁻¹ = u * v := by rw [hw', hwv]
  have czu : z * u * z⁻¹ = v := by rw [hz', hzu]
  have czv : z * v * z⁻¹ = u := by rw [← czu, conj_conj_of_sq hz]
  refine commute_pow_three_of_cycle (x₁ := u * v) (x₂ := v) ?_ ?_ ?_
  · rw [conj_mul_mul, czu, cwv]
  · rw [conj_mul_mul, show z * (u * v) * z⁻¹ = (z * u * z⁻¹) * (z * v * z⁻¹) by group, czu,
      czv, show w * (v * u) * w⁻¹ = (w * v * w⁻¹) * (w * u * w⁻¹) by group, cwv, cwu, mul_assoc,
      ← huv.eq, ← mul_assoc, hu, one_mul]
  · rw [conj_mul_mul, czv, cwu]

theorem commute_pow_three_of_orbit {a z p : G} (ha : a * a = 1) (hz : z * z = 1)
    (haz : (a * z) ^ 3 = 1) (hap : Commute a p) (hpq : Commute p (z * p * z)) :
    Commute ((z * (a * p)) ^ 3) p := by
  have ha' : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  have hz' : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz
  set q := z * p * z with hq
  set r := a * q * a with hr
  have hbraid : z * a * z = a * z * a := by
    have h : a * z * a * (z * a * z) = 1 := by
      rw [← haz, pow_three]; simp only [mul_assoc]
    rw [eq_inv_of_mul_eq_one_right h]
    simp only [mul_inv_rev, ha', hz', mul_assoc]
  have hapa : a * p * a = p := by rw [hap.eq, mul_assoc, ha, mul_one]
  have cpp : p * p * p⁻¹ = p := by group
  have cap : a * p * a⁻¹ = p := by rw [hap.eq, mul_inv_cancel_right]
  have cpa : p * a * p⁻¹ = a := by rw [← hap.eq, mul_inv_cancel_right]
  have czp : z * p * z⁻¹ = q := by rw [hz']
  have cpq : p * q * p⁻¹ = q := by rw [hpq.eq, mul_inv_cancel_right]
  have caq : a * q * a⁻¹ = r := by rw [ha']
  have czr : z * r * z⁻¹ = r := by
    rw [hz', hr, hq]
    calc z * (a * (z * p * z) * a) * z = (z * a * z) * p * (z * a * z) := by group
      _ = (a * z * a) * p * (a * z * a) := by rw [hbraid]
      _ = a * z * (a * p * a) * z * a := by group
      _ = a * (z * p * z) * a := by rw [hapa]; group
  have cpr : p * r * p⁻¹ = r := by
    rw [hr, show p * (a * q * a) * p⁻¹ = (p * a * p⁻¹) * (p * q * p⁻¹) * (p * a * p⁻¹) by group,
      cpq, cpa]
  have car : a * r * a⁻¹ = q := by
    rw [hr, show a * (a * q * a) * a⁻¹ = (a * a) * q * (a * a⁻¹) by group, ha, mul_inv_cancel,
      one_mul, mul_one]
  have czq : z * q * z⁻¹ = p := by rw [← czp, conj_conj_of_sq hz]
  refine commute_pow_three_of_cycle (x₁ := q) (x₂ := r) ?_ ?_ ?_
  · rw [conj_mul_mul z (a * p), conj_mul_mul a p, cpp, cap, czp]
  · rw [conj_mul_mul z (a * p), conj_mul_mul a p, cpq, caq, czr]
  · rw [conj_mul_mul z (a * p), conj_mul_mul a p, cpr, car, czq]

theorem odd_orderOf_mul_of_four_group (hD : IsRootInvolutionSet D) {w z u v : G} (hwD : w ∈ D)
    (hzD : z ∈ D) (hu : u * u = 1) (huv : Commute u v) (hwu : Commute w u)
    (hwv : w * v * w = u * v) (hzu : z * u * z = v) (hv : v ≠ 1) : Odd (orderOf (w * z)) := by
  have hw := hD.mul_self_eq_one hwD
  have hz := hD.mul_self_eq_one hzD
  have hc := commute_pow_three_of_four_group hw hz hu huv hwu hwv hzu
  have e1 : SemiconjBy (w * z) u (u * v) := by
    have hzu' : z * u = v * z := by rw [← hzu]; simp only [mul_assoc, hz, mul_one]
    have hwv' : w * v = u * v * w := by rw [← hwv]; simp only [mul_assoc, hw, mul_one]
    show w * z * u = u * v * (w * z)
    rw [mul_assoc, hzu', ← mul_assoc, hwv', mul_assoc]
  have h4 : SemiconjBy ((w * z) ^ 4) u (u * v) := by
    rw [show (4 : ℕ) = 3 + 1 from rfl, pow_succ']
    exact e1.mul_left hc
  rcases hD.orderOf_mul hwD hzD with h | h | h
  · exfalso
    have h1 : (w * z) ^ 4 = 1 := by
      rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, ← h, pow_orderOf_eq_one, one_pow]
    rw [h1] at h4
    have : u = u * v := by simpa [SemiconjBy] using h4
    exact hv (left_eq_mul.mp this)
  · exfalso
    have h1 : (w * z) ^ 4 = 1 := by rw [← h, pow_orderOf_eq_one]
    rw [h1] at h4
    have : u = u * v := by simpa [SemiconjBy] using h4
    exact hv (left_eq_mul.mp this)
  · exact h

variable [Finite G]

theorem pow_three_eq_one_of_four_group {w z u v : G} (hw : w * w = 1) (hz : z * z = 1)
    (hu : u * u = 1) (huv : Commute u v) (hwu : Commute w u) (hwv : w * v * w = u * v)
    (hzu : z * u * z = v) (hwQ : w ∈ Moufang.twoCore u) (hodd : Odd (orderOf (w * z))) :
    (w * z) ^ 3 = 1 := by
  exact eq_one_of_mem_twoCore_of_inv hwQ (commute_pow_three_of_four_group hw hz hu huv hwu hwv hzu)
    (conj_pow_mul_left_eq_inv hw hz 3) (Odd.of_dvd_nat hodd (orderOf_pow_dvd 3))

theorem pow_three_eq_one_of_orbit (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g})
    (hD : IsRootInvolutionSet D) {a z p : G} (ha : a ∈ D) (hz : z ∈ D) (hp : p ∈ D)
    (h3 : (a * z) ^ 3 = 1) (haz : ¬ Commute a z) (hap : Commute a p) (hapD : a * p ∈ D)
    (h4 : orderOf (z * p) = 4) : (z * (a * p)) ^ 3 = 1 := by
  have ha2 := hD.mul_self_eq_one ha
  have hz2 := hD.mul_self_eq_one hz
  have hp2 := hD.mul_self_eq_one hp
  have hw2 := hD.mul_self_eq_one hapD
  have hpq : Commute p (z * p * z) := by
    have h4' : orderOf (p * z) = 4 := by rwa [orderOf_mul_comm_eq]
    obtain ⟨-, -, -, h⟩ := sq_mem_of_orderOf_eq_four hD hp hz h4'
    have hc := (sq_mem_of_orderOf_eq_four hD hp hz h4').2.1
    rw [h]
    exact (Commute.refl p).mul_right hc
  have hc := commute_pow_three_of_orbit ha2 hz2 h3 hap hpq
  have hwQ : a * p ∈ Moufang.twoCore p := by
    refine mem_twoCore_of_collinear hclass hD hp hapD (hap.mul_left (Commute.refl p)) ?_
    rwa [mul_assoc, hp2, mul_one]
  have hodd3 : Odd (orderOf (a * z)) :=
    Odd.of_dvd_nat (by decide : Odd 3) (orderOf_dvd_of_pow_eq_one h3)
  obtain ⟨-, hodd⟩ := opposite_of_opposite_of_special_of_line hclass hD ha hp hap hapD hz haz
    hodd3 h4
  have hodd' : Odd (orderOf (z * (a * p))) := by rwa [orderOf_mul_comm_eq]
  exact eq_one_of_mem_twoCore_of_inv hwQ hc (conj_pow_mul_right_eq_inv hw2 hz2 3)
    (Odd.of_dvd_nat hodd' (orderOf_pow_dvd 3))

end CFSG.Timmesfeld.Bridge
