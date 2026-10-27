module

public import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic.Group
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific

public section

namespace CFSG.RankThree.GF2n.Stroth80

open scoped commutatorElement

variable {X : Type*} [Group X]

theorem orbit_prod_mem_of_order_three {N Z0 : Subgroup X} (hZ3 : ∀ z ∈ Z0, z ^ 3 = 1 → z = 1)
    (hNN : ∀ a ∈ N, ∀ b ∈ N, ⁅a, b⁆ ∈ Z0) {y : X} (hy3 : y ^ 3 = 1)
    (hyN : ∀ a ∈ N, y * a * y⁻¹ ∈ N) (hyZ : ∀ z ∈ Z0, y * z = z * y)
    (hCy : ∀ a ∈ N, y * a = a * y → a ∈ Z0) {m : X} (hm : m ∈ N) :
    m * (y * m * y⁻¹) * (y ^ 2 * m * (y ^ 2)⁻¹) ∈ Z0 := by
  have ha : y * m * y⁻¹ ∈ N := hyN m hm
  have hb : y ^ 2 * m * (y ^ 2)⁻¹ ∈ N := by
    have := hyN _ ha
    rw [pow_two]
    simpa [mul_assoc] using this
  set a := y * m * y⁻¹ with hadef
  set b := y ^ 2 * m * (y ^ 2)⁻¹ with hbdef
  set w := m * a * b with hwdef
  have hwN : w ∈ N := N.mul_mem (N.mul_mem hm ha) hb
  have hya : y * a * y⁻¹ = b := by
    rw [hadef, hbdef, pow_two]
    group
  have hyb : y * b * y⁻¹ = m := by
    have e : y * b * y⁻¹ = y ^ 3 * m * (y ^ 3)⁻¹ := by
      rw [hbdef]
      group
    rw [e, hy3]
    group
  have hyw : y * w * y⁻¹ = a * b * m := by
    have e : y * w * y⁻¹ = (y * m * y⁻¹) * (y * a * y⁻¹) * (y * b * y⁻¹) := by
      rw [hwdef]
      group
    rw [e, hya, hyb]
  set z := ⁅a * b, m⁆ with hzdef
  have hzZ : z ∈ Z0 := hNN _ (N.mul_mem ha hb) _ hm
  have hzw : y * w * y⁻¹ = z * w := by
    rw [hyw, hzdef, hwdef]
    simp only [commutatorElement_def]
    group
  have hz1 : y * z * y⁻¹ = z := by
    rw [hyZ z hzZ]
    group
  have hz2 : y ^ 2 * w * (y ^ 2)⁻¹ = z * z * w := by
    have e : y ^ 2 * w * (y ^ 2)⁻¹ = y * (y * w * y⁻¹) * y⁻¹ := by
      rw [pow_two]
      group
    rw [e, hzw]
    have e2 : y * (z * w) * y⁻¹ = (y * z * y⁻¹) * (y * w * y⁻¹) := by group
    rw [e2, hz1, hzw, mul_assoc]
  have hz3 : y ^ 3 * w * (y ^ 3)⁻¹ = z * z * z * w := by
    have e : y ^ 3 * w * (y ^ 3)⁻¹ = y * (y ^ 2 * w * (y ^ 2)⁻¹) * y⁻¹ := by
      rw [show (3 : ℕ) = 2 + 1 from rfl, pow_succ']
      group
    rw [e, hz2]
    have e2 : y * (z * z * w) * y⁻¹ =
        (y * z * y⁻¹) * (y * z * y⁻¹) * (y * w * y⁻¹) := by group
    rw [e2, hz1, hzw]
    group
  have hzcube : z ^ 3 = 1 := by
    rw [hy3] at hz3
    have h1 : w = z * z * z * w := by simpa using hz3
    have h2 : z * z * z = 1 := by
      have := congrArg (fun g => g * w⁻¹) h1
      simpa [mul_assoc] using this.symm
    rw [show (3 : ℕ) = 2 + 1 from rfl, pow_succ, pow_two]
    exact h2
  have hz : z = 1 := hZ3 z hzZ hzcube
  apply hCy w hwN
  have h := hzw
  rw [hz, one_mul] at h
  calc y * w = y * w * y⁻¹ * y := by group
    _ = w * y := by rw [h]

theorem exists_comm_eq_of_order_three {N Z0 : Subgroup X} (hZN : Z0 ≤ N)
    (hN2 : ∀ a ∈ N, ∃ k : ℕ, a ^ (2 ^ k) = 1) (hNN : ∀ a ∈ N, ∀ b ∈ N, ⁅a, b⁆ ∈ Z0)
    (hZc : ∀ z ∈ Z0, ∀ a ∈ N, a * z = z * a) {y x : X} (hy3 : y ^ 3 = 1)
    (hyN : ∀ a ∈ N, y * a * y⁻¹ ∈ N) (hyZ : ∀ z ∈ Z0, y * z = z * y)
    (hCy : ∀ a ∈ N, y * a = a * y → a ∈ Z0) (hxy : x * y = y * x)
    (hxN : ∀ a ∈ N, ⁅a, x⁆ ∈ Z0) :
    ∀ m ∈ N, ∃ z ∈ Z0, ⁅m, x⁆ = ⁅z, x⁆ := by
  intro m hm
  have hZ3 : ∀ z ∈ Z0, z ^ 3 = 1 → z = 1 := by
    intro z hz hz3
    obtain ⟨k, hk⟩ := hN2 z (hZN hz)
    have h1 : orderOf z ∣ 3 := orderOf_dvd_of_pow_eq_one hz3
    have h2 : orderOf z ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk
    have h3 : orderOf z ∣ Nat.gcd 3 (2 ^ k) := Nat.dvd_gcd h1 h2
    have hcop : Nat.gcd 3 (2 ^ k) = 1 :=
      Nat.Coprime.pow_right k (by decide : Nat.Coprime 3 2)
    rw [hcop, Nat.dvd_one, orderOf_eq_one_iff] at h3
    exact h3
  have hw := orbit_prod_mem_of_order_three hZ3 hNN hy3 hyN hyZ hCy hm
  have hmul : ∀ a ∈ N, ∀ b ∈ N, ⁅a * b, x⁆ = ⁅a, x⁆ * ⁅b, x⁆ := by
    intro a ha b hb
    have e : ⁅a * b, x⁆ = (a * ⁅b, x⁆ * a⁻¹) * ⁅a, x⁆ := by
      simp only [commutatorElement_def]
      group
    have h1 : a * ⁅b, x⁆ * a⁻¹ = ⁅b, x⁆ := by
      rw [hZc _ (hxN b hb) a ha]
      group
    rw [e, h1]
    exact (hZc _ (hxN b hb) _ (hZN (hxN a ha))).symm
  have hconj : ∀ a ∈ N, ⁅y * a * y⁻¹, x⁆ = ⁅a, x⁆ := by
    intro a ha
    have hx' : y⁻¹ * x * y = x := by
      calc y⁻¹ * x * y = y⁻¹ * (x * y) := by group
        _ = y⁻¹ * (y * x) := by rw [hxy]
        _ = x := by group
    have e : ⁅y * a * y⁻¹, x⁆ = y * ⁅a, y⁻¹ * x * y⁆ * y⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [e, hx', hyZ _ (hxN a ha)]
    group
  have ha : y * m * y⁻¹ ∈ N := hyN m hm
  have hconj2 : ⁅y ^ 2 * m * (y ^ 2)⁻¹, x⁆ = ⁅m, x⁆ := by
    have e : y ^ 2 * m * (y ^ 2)⁻¹ = y * (y * m * y⁻¹) * y⁻¹ := by
      rw [pow_two]
      group
    rw [e, hconj _ ha, hconj _ hm]
  have hb : y ^ 2 * m * (y ^ 2)⁻¹ ∈ N := by
    have := hyN _ ha
    rw [pow_two]
    simpa [mul_assoc] using this
  have hwx : ⁅m * (y * m * y⁻¹) * (y ^ 2 * m * (y ^ 2)⁻¹), x⁆ = ⁅m, x⁆ ^ 3 := by
    rw [hmul _ (N.mul_mem hm ha) _ hb, hmul _ hm _ ha, hconj _ hm, hconj2]
    rw [show (3 : ℕ) = 2 + 1 from rfl, pow_succ, pow_two]
  set c := ⁅m, x⁆ with hcdef
  obtain ⟨k, hk⟩ := hN2 c (hZN (hxN m hm))
  have hcop : Nat.Coprime 3 (orderOf c) := by
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hk)
    rw [hj]
    exact Nat.Coprime.pow_right j (by decide : Nat.Coprime 3 2)
  obtain ⟨e, he⟩ := exists_pow_eq_self_of_coprime hcop
  set w := m * (y * m * y⁻¹) * (y ^ 2 * m * (y ^ 2)⁻¹) with hwdef
  have hwN : w ∈ N := hZN hw
  have hpow : ∀ j : ℕ, ⁅w ^ j, x⁆ = ⁅w, x⁆ ^ j := by
    intro j
    induction j with
    | zero => simp [commutatorElement_def]
    | succ j ih => rw [pow_succ, hmul _ (N.pow_mem hwN j) _ hwN, ih, pow_succ]
  refine ⟨w ^ e, Z0.pow_mem hw e, ?_⟩
  rw [hpow, hwx, he]

end CFSG.RankThree.GF2n.Stroth80
