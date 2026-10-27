module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8Base
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Tactic.Group
public import Mathlib.Tactic.FinCases
public import Mathlib.Data.Nat.SuccPred

public section

namespace CFSG.Quasithin.Fan86.F87

section Comm

variable {H : Type*} [Group H]

theorem fcomm_inv_eq (a b : H) : (fcomm a b)⁻¹ = fcomm b a := by
  unfold fcomm
  group

theorem fcomm_eq_one_iff {a b : H} : fcomm a b = 1 ↔ a * b = b * a := by
  unfold fcomm
  constructor
  · intro h
    calc a * b = (b * a) * (a⁻¹ * b⁻¹ * a * b) := by group
      _ = b * a := by rw [h, mul_one]
  · intro h
    calc a⁻¹ * b⁻¹ * a * b = a⁻¹ * b⁻¹ * (a * b) := by group
      _ = a⁻¹ * b⁻¹ * (b * a) := by rw [h]
      _ = 1 := by group

theorem fcomm_mul_left (a b c : H) : fcomm (a * b) c = b⁻¹ * fcomm a c * b * fcomm b c := by
  unfold fcomm
  group

theorem fcomm_mul_right (a b c : H) : fcomm a (b * c) = fcomm a c * (c⁻¹ * fcomm a b * c) := by
  unfold fcomm
  group

theorem sq_mul (Y h : H) (hc : Commute (fcomm h Y) h) :
    (Y * h) * (Y * h) = (Y * Y) * (h * h) * fcomm h Y := by
  calc Y * h * (Y * h) = Y * Y * h * fcomm h Y * h := by
        unfold fcomm
        group
    _ = Y * Y * h * (fcomm h Y * h) := by rw [mul_assoc (Y * Y * h)]
    _ = Y * Y * h * (h * fcomm h Y) := by rw [hc.eq]
    _ = (Y * Y) * (h * h) * fcomm h Y := by group

end Comm

section CommGroupLemmas

variable {A : Type*} [CommGroup A]

theorem sq_aux (p q z ε r s : A) (hz : z * z = 1) :
    p * q * z * (ε * (r * (s * z))) = p * q * (s * r) * ε := by
  have : p * q * z * (ε * (r * (s * z))) = p * q * (s * r) * ε * (z * z) := by ac_rfl
  rw [this, hz, mul_one]

theorem not_mem_span_aux {zi zj zt zp zq z : A} (hi : zi * zi = 1) (hj : zj * zj = 1)
    (ht : zt * zt = 1) (hz : z * z = 1)
    (hR : zi * zj * zt * zp * zq = 1) (h1 : zt ≠ 1) (h2 : zt ≠ zi) (h3 : zt ≠ zj) (h4 : zt ≠ z)
    (h5 : zt * zi * zj ≠ 1) (h6 : zt * zi * z ≠ 1) (h7 : zt * zj * z ≠ 1)
    (h8 : zp * zq * z ≠ 1) (e₁ e₂ e₃ : Fin 2) :
    zt ≠ zi ^ (e₁ : ℕ) * zj ^ (e₂ : ℕ) * z ^ (e₃ : ℕ) := by
  have hpq : zp * zq = zi * zj * zt := by
    have h : zp * zq * (zi * zj * zt) = 1 := by rw [← hR]; ac_rfl
    have h' := eq_inv_of_mul_eq_one_left h
    rw [h', mul_inv_rev, mul_inv_rev, inv_eq_of_mul_eq_one_right hi,
      inv_eq_of_mul_eq_one_right hj, inv_eq_of_mul_eq_one_right ht]
    ac_rfl
  fin_cases e₁ <;> fin_cases e₂ <;> fin_cases e₃ <;> intro h <;>
    simp only [pow_zero, pow_one, mul_one, one_mul] at h
  · exact h1 h
  · exact h4 h
  · exact h3 h
  · apply h7
    rw [h]
    calc zj * z * zj * z = (zj * zj) * (z * z) := by ac_rfl
      _ = 1 := by rw [hj, hz, mul_one]
  · exact h2 h
  · apply h6
    rw [h]
    calc zi * z * zi * z = (zi * zi) * (z * z) := by ac_rfl
      _ = 1 := by rw [hi, hz, mul_one]
  · apply h5
    rw [h]
    calc zi * zj * zi * zj = (zi * zi) * (zj * zj) := by ac_rfl
      _ = 1 := by rw [hi, hj, mul_one]
  · apply h8
    rw [hpq, h]
    calc zi * zj * (zi * zj * z) * z = (zi * zi) * (zj * zj) * (z * z) := by ac_rfl
      _ = 1 := by rw [hi, hj, hz, mul_one, mul_one]

theorem pow_mod_two {x : A} (hx : x * x = 1) (n : ℕ) : x ^ n = x ^ (n % 2) := by
  calc x ^ n = x ^ (n % 2 + 2 * (n / 2)) := by rw [Nat.mod_add_div]
    _ = x ^ (n % 2) := by rw [pow_add, pow_mul, pow_two, hx, one_pow, mul_one]

theorem not_mem_span_nat {zi zj zt zp zq z : A} (hi : zi * zi = 1) (hj : zj * zj = 1)
    (ht : zt * zt = 1) (hz : z * z = 1) (hR : zi * zj * zt * zp * zq = 1) (h1 : zt ≠ 1)
    (h2 : zt ≠ zi) (h3 : zt ≠ zj) (h4 : zt ≠ z) (h5 : zt * zi * zj ≠ 1) (h6 : zt * zi * z ≠ 1)
    (h7 : zt * zj * z ≠ 1) (h8 : zp * zq * z ≠ 1) (n₁ n₂ n₃ : ℕ) :
    zt ≠ zi ^ n₁ * zj ^ n₂ * z ^ n₃ := by
  rw [pow_mod_two hi n₁, pow_mod_two hj n₂, pow_mod_two hz n₃]
  exact not_mem_span_aux hi hj ht hz hR h1 h2 h3 h4 h5 h6 h7 h8 ⟨n₁ % 2, Nat.mod_lt _ (by norm_num)⟩
    ⟨n₂ % 2, Nat.mod_lt _ (by norm_num)⟩ ⟨n₃ % 2, Nat.mod_lt _ (by norm_num)⟩

theorem rel_reduce {zi zj zt z : A} (hi : zi * zi = 1) (hj : zj * zj = 1) (hz : z * z = 1)
    (a b f n₁ n₂ n₃ : ℕ) (h : zt * (zi ^ a * zj ^ b) * z ^ f = zi ^ n₁ * zj ^ n₂ * z ^ n₃) :
    zt = zi ^ (n₁ + a) * zj ^ (n₂ + b) * z ^ (n₃ + f) := by
  have hsq : ∀ {x : A}, x * x = 1 → ∀ m : ℕ, x ^ m * x ^ m = 1 := fun hx m => by
    rw [← mul_pow, hx, one_pow]
  have hw : (zi ^ a * zj ^ b * z ^ f) * (zi ^ a * zj ^ b * z ^ f) = 1 := by
    calc (zi ^ a * zj ^ b * z ^ f) * (zi ^ a * zj ^ b * z ^ f)
        = (zi ^ a * zi ^ a) * (zj ^ b * zj ^ b) * (z ^ f * z ^ f) := by ac_rfl
      _ = 1 := by rw [hsq hi, hsq hj, hsq hz, one_mul, one_mul]
  calc zt = zt * ((zi ^ a * zj ^ b * z ^ f) * (zi ^ a * zj ^ b * z ^ f)) := by rw [hw, mul_one]
    _ = (zt * (zi ^ a * zj ^ b) * z ^ f) * (zi ^ a * zj ^ b * z ^ f) := by ac_rfl
    _ = zi ^ (n₁ + a) * zj ^ (n₂ + b) * z ^ (n₃ + f) := by
      rw [h, pow_add, pow_add, pow_add]
      ac_rfl

theorem no_rel_nat {zi zj zt zp zq z : A} (hi : zi * zi = 1) (hj : zj * zj = 1)
    (ht : zt * zt = 1) (hz : z * z = 1) (hR : zi * zj * zt * zp * zq = 1) (h1 : zt ≠ 1)
    (h2 : zt ≠ zi) (h3 : zt ≠ zj) (h4 : zt ≠ z) (h5 : zt * zi * zj ≠ 1) (h6 : zt * zi * z ≠ 1)
    (h7 : zt * zj * z ≠ 1) (h8 : zp * zq * z ≠ 1) (a b f n₁ n₂ n₃ : ℕ) :
    zt * (zi ^ a * zj ^ b) * z ^ f ≠ zi ^ n₁ * zj ^ n₂ * z ^ n₃ := fun h =>
  not_mem_span_nat hi hj ht hz hR h1 h2 h3 h4 h5 h6 h7 h8 (n₁ + a) (n₂ + b) (n₃ + f)
    (rel_reduce hi hj hz a b f n₁ n₂ n₃ h)

theorem quad3 {zi zj za zb zm : A} (hi : zi * zi = 1) (hj : zj * zj = 1) (hm : zm * zm = 1)
    (hR : zi * zj * za * zb * zm = 1) :
    zj * zi * (za * zb) = zm ∧ zb * zj * (za * zm) = zi ∧ za * zi * (zb * zm) = zj := by
  refine ⟨?_, ?_, ?_⟩
  · have h : zm * (zj * zi * (za * zb)) = 1 := by rw [← hR]; ac_rfl
    exact (inv_eq_of_mul_eq_one_right h).symm.trans (inv_eq_of_mul_eq_one_right hm)
  · have h : zi * (zb * zj * (za * zm)) = 1 := by rw [← hR]; ac_rfl
    exact (inv_eq_of_mul_eq_one_right h).symm.trans (inv_eq_of_mul_eq_one_right hi)
  · have h : zj * (za * zi * (zb * zm)) = 1 := by rw [← hR]; ac_rfl
    exact (inv_eq_of_mul_eq_one_right h).symm.trans (inv_eq_of_mul_eq_one_right hj)

theorem prodFive_perm (f : Fin 5 → A) {σ : Fin 5 → Fin 5} (hσ : Function.Injective σ) :
    prodFive f = f (σ 0) * f (σ 1) * f (σ 2) * f (σ 3) * f (σ 4) := by
  have hb := Finite.injective_iff_bijective.1 hσ
  calc prodFive f = ∏ s, f s := by simp [prodFive, Fin.prod_univ_five]
    _ = ∏ s, f (σ s) := (Fintype.prod_bijective σ hb (fun s => f (σ s)) f (fun _ => rfl)).symm
    _ = _ := by simp [Fin.prod_univ_five]

theorem prodFive_reindex (f : Fin 5 → A) {i j : Fin 5} (hij : i ≠ j) :
    prodFive f = f i * f j * f (kstar i j) * f (kstar j i) * f (midlab i j) := by
  have hinj : ∀ i j : Fin 5, i ≠ j →
      Function.Injective (![i, j, kstar i j, kstar j i, midlab i j] : Fin 5 → Fin 5) := by
    unfold kstar midlab
    decide
  simpa using prodFive_perm f (hinj i j hij)

end CommGroupLemmas

end CFSG.Quasithin.Fan86.F87
