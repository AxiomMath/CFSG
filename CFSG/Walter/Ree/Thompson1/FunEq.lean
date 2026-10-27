module

public import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic.ReduceModChar

public section

namespace CFSG.Walter.Ree.Thompson1

variable {K : Type*} [Field K]

section Defs

variable (σ : K ≃+* K)

@[expose] def pw (x : K) : K := x ^ 2 * σ x

@[expose] def kk (y : K) : K := (y - 1) * (y - σ y)

@[expose] def Eq19 (f : K → K) : Prop :=
  ∀ x y, f (y / x) * pw σ x + f (x + y) - f x - f (y / (1 + x)) * pw σ (1 + x) = 0

end Defs

structure Norm18 (f : K → K) : Prop where
  zero : f 0 = 0
  one : f 1 = 0
  neg_one : f (-1) = 0

section Basic

variable {σ : K ≃+* K}

theorem pw_zero : pw σ (0 : K) = 0 := by simp [pw]

theorem pw_one : pw σ (1 : K) = 1 := by simp [pw]

theorem pw_neg (x : K) : pw σ (-x) = -pw σ x := by simp [pw]

theorem pw_mul (x y : K) : pw σ (x * y) = pw σ x * pw σ y := by simp [pw]; ring

theorem pw_inv (x : K) : pw σ x⁻¹ = (pw σ x)⁻¹ := by simp [pw, mul_comm]

theorem pw_div (x y : K) : pw σ (x / y) = pw σ x / pw σ y := by
  simp [pw, div_eq_mul_inv]; ring

theorem pw_pow (x : K) (n : ℕ) : pw σ (x ^ n) = pw σ x ^ n := by simp [pw]; ring

theorem pw_ne_zero {x : K} (hx : x ≠ 0) : pw σ x ≠ 0 := by simp [pw, hx]

end Basic

section CharThree

variable [CharP K 3] {σ : K ≃+* K}

theorem pw_id1 (y : K) : pw σ y - 1 + pw σ (1 - y) = (1 + y) * (y - σ y) := by
  simp only [pw, map_sub, map_one]
  linear_combination (norm := skip)
  ring_nf
  reduce_mod_char!

theorem pw_id2 (y : K) : 1 + pw σ y - pw σ (1 + y) = (1 - y) * (y - σ y) := by
  simp only [pw, map_add, map_one]
  linear_combination (norm := skip)
  ring_nf
  reduce_mod_char!

theorem pw_id3 (y : K) :
    (y ^ 2 - 1) * (1 - pw σ y) + (y + 1) ^ 2 * pw σ (1 + y) =
      (y + 1) * (y + σ y) * (y ^ 2 + 1) := by
  simp only [pw, map_add, map_one]
  linear_combination (norm := skip)
  ring_nf
  reduce_mod_char!

end CharThree

section Derived

variable {σ : K ≃+* K} {f : K → K} (h19 : Eq19 σ f) (h18 : Norm18 f)
include h19 h18

theorem eq20 (x : K) : f ((-1 - x) / x) * pw σ x = f x := by
  have h := h19 x (-1 - x)
  have e1 : x + (-1 - x) = -1 := by ring
  have e2 : f ((-1 - x) / (1 + x)) = 0 := by
    rcases eq_or_ne (1 + x) 0 with hx | hx
    · rw [hx, div_zero, h18.zero]
    · rw [show (-1 - x) / (1 + x) = -1 by field_simp; ring, h18.neg_one]
  rw [e1, h18.neg_one, e2] at h
  linear_combination h

theorem eq21 (x : K) : f x + f (-x / (1 + x)) * pw σ (1 + x) = 0 := by
  have h := h19 x (-x)
  have e1 : x + -x = 0 := by ring
  have e2 : f (-x / x) * pw σ x = 0 := by
    rcases eq_or_ne x 0 with hx | hx
    · rw [hx, pw_zero, mul_zero]
    · rw [show -x / x = -1 by field_simp, h18.neg_one, zero_mul]
  rw [e1, h18.zero] at h
  linear_combination -h + e2

theorem eq23 (u : K) : f u⁻¹ = f u * (pw σ u)⁻¹ := by
  rcases eq_or_ne u 0 with hu | hu
  · simp [hu, h18.zero]
  rcases eq_or_ne u (-1) with hu1 | hu1
  · simp [hu1, h18.neg_one]
  have hu1' : 1 + u ≠ 0 := fun h => hu1 (by linear_combination h)
  set x : K := -1 / (1 + u) with hxdef
  have hx0 : x ≠ 0 := by simp [hxdef, hu1']
  have h1x : 1 + x = u / (1 + u) := by rw [hxdef]; field_simp; ring
  have h1x0 : 1 + x ≠ 0 := by rw [h1x]; exact div_ne_zero hu hu1'
  have e20 := eq20 h19 h18 x
  have e21 := eq21 h19 h18 x
  have ea : (-1 - x) / x = u := by rw [hxdef]; field_simp; ring
  have eb : -x / (1 + x) = u⁻¹ := by rw [h1x, hxdef]; field_simp
  rw [ea] at e20
  rw [eb] at e21
  have hpx : pw σ x = -(pw σ (1 + u))⁻¹ := by
    rw [hxdef, neg_div, pw_neg, one_div, pw_inv]
  have hp1x : pw σ (1 + x) = pw σ u * (pw σ (1 + u))⁻¹ := by
    rw [h1x, pw_div, div_eq_mul_inv]
  rw [hpx] at e20
  rw [hp1x, ← e20] at e21
  have hpu : pw σ u ≠ 0 := pw_ne_zero hu
  have hp1u : pw σ (1 + u) ≠ 0 := pw_ne_zero hu1'
  field_simp at e21 ⊢
  linear_combination e21

theorem eq23' (x y : K) : f (x / y) * pw σ y = f (y / x) * pw σ x := by
  rcases eq_or_ne x 0 with hx | hx
  · simp [hx, h18.zero, pw_zero]
  rcases eq_or_ne y 0 with hy | hy
  · simp [hy, h18.zero, pw_zero]
  rw [show x / y = (y / x)⁻¹ by rw [inv_div], eq23 h19 h18, pw_div]
  have := pw_ne_zero (σ := σ) hx
  have := pw_ne_zero (σ := σ) hy
  field_simp

theorem eq24 (x y : K) :
    f (y / x) * pw σ x + f (x + y) - f y - f (x / (1 + y)) * pw σ (1 + y) = 0 := by
  have h := h19 y x
  rw [eq23' h19 h18, add_comm y x] at h
  exact h

theorem eq25 (x y : K) :
    f x + f (y / (1 + x)) * pw σ (1 + x) = f y + f (x / (1 + y)) * pw σ (1 + y) := by
  linear_combination eq24 h19 h18 x y - h19 x y

theorem eq26 (x : K) : f x = f (-1 - x) := by
  have h := eq25 h19 h18 x (-1 - x)
  have e2 : f ((-1 - x) / (1 + x)) = 0 := by
    rcases eq_or_ne (1 + x) 0 with hx | hx
    · rw [hx, div_zero, h18.zero]
    · rw [show (-1 - x) / (1 + x) = -1 by field_simp; ring, h18.neg_one]
  have e3 : f (x / (1 + (-1 - x))) = 0 := by
    rw [show (1 : K) + (-1 - x) = -x by ring]
    rcases eq_or_ne x 0 with hx | hx
    · rw [hx, neg_zero, div_zero, h18.zero]
    · rw [show x / -x = -1 by field_simp, h18.neg_one]
  rw [e2, e3] at h
  linear_combination h

theorem eq28 (y : K) : f (-y ^ 2) + f y * pw σ y = f y + f (-y) * pw σ (1 + y) := by
  have h := eq25 h19 h18 (y ^ 2 - 1) y
  have e1 : f (y ^ 2 - 1) = f (-y ^ 2) := by rw [eq26 h19 h18 (y ^ 2 - 1)]; ring_nf
  have e2 : f (y / (1 + (y ^ 2 - 1))) * pw σ (1 + (y ^ 2 - 1)) = f y * pw σ y := by
    rw [show (1 : K) + (y ^ 2 - 1) = y ^ 2 by ring]
    rcases eq_or_ne y 0 with hy | hy
    · simp [hy, h18.zero, pw_zero]
    rw [show y / y ^ 2 = y⁻¹ by field_simp, eq23 h19 h18, pw_pow]
    have := pw_ne_zero (σ := σ) hy
    field_simp
  have e3 : f ((y ^ 2 - 1) / (1 + y)) * pw σ (1 + y) = f (-y) * pw σ (1 + y) := by
    rcases eq_or_ne (1 + y) 0 with hy | hy
    · rw [hy, pw_zero, mul_zero, mul_zero]
    rw [show (y ^ 2 - 1) / (1 + y) = y - 1 by field_simp; ring, eq26 h19 h18 (y - 1)]
    ring_nf
  rw [e1, e2, e3] at h
  exact h

omit h19 in
theorem eq_zero_of_fixed (hfix : ∀ x : K, σ x = x → x = 0 ∨ x = 1 ∨ x = -1) {y : K}
    (hy : σ y = y) : f y = 0 := by
  rcases hfix y hy with rfl | rfl | rfl
  · exact h18.zero
  · exact h18.one
  · exact h18.neg_one

section Three

variable [CharP K 3] (hfix : ∀ x : K, σ x = x → x = 0 ∨ x = 1 ∨ x = -1)
include hfix

theorem eq29 (y : K) : f y * (y + 1) = f (-y) * (y - 1) := by
  rcases eq_or_ne (σ y) y with hy | hy
  · have hy' : σ (-y) = -y := by simp [hy]
    rw [eq_zero_of_fixed h18 hfix hy, eq_zero_of_fixed h18 hfix hy']
    ring
  have h1 := eq28 h19 h18 y
  have h2 := eq28 h19 h18 (-y)
  rw [neg_neg, neg_sq, pw_neg, show (1 : K) + -y = 1 - y by ring] at h2
  have i1 := pw_id1 (σ := σ) y
  have i2 := pw_id2 (σ := σ) y
  have hne : y - σ y ≠ 0 := sub_ne_zero.2 (Ne.symm hy)
  have key : (y - σ y) * (f y * (y + 1) - f (-y) * (y - 1)) = 0 := by
    linear_combination h1 - h2 - f y * i1 - f (-y) * i2
  rcases mul_eq_zero.1 key with h | h
  · exact absurd h hne
  · linear_combination h

theorem eq_zero_sub_one {z : K} (hz : f z = 0) : f (z - 1) = 0 := by
  rw [eq26 h19 h18 (z - 1), show -1 - (z - 1) = -z by ring]
  rcases eq_or_ne z 1 with rfl | hz1
  · exact h18.neg_one
  have h := eq29 h19 h18 hfix z
  rw [hz, zero_mul] at h
  exact (mul_eq_zero.1 h.symm).resolve_right (sub_ne_zero.2 hz1)

variable (hsq : ∀ x : K, x ^ 2 ≠ -1)
include hsq

theorem eq30 (y : K) : f (y ^ 2) = f y * (y + 1) * (y + σ y) := by
  have e1 := eq29 h19 h18 hfix (y ^ 2)
  have e2 := eq28 h19 h18 y
  have e3 := eq29 h19 h18 hfix y
  have i3 := pw_id3 (σ := σ) y
  have hne : y ^ 2 + 1 ≠ 0 := fun h => hsq y (by linear_combination h)
  have key : (f (y ^ 2) - f y * (y + 1) * (y + σ y)) * (y ^ 2 + 1) = 0 := by
    linear_combination e1 + (y ^ 2 - 1) * e2 - (y + 1) * pw σ (1 + y) * e3 + f y * i3
  rcases mul_eq_zero.1 key with h | h
  · linear_combination h
  · exact absurd h hne

theorem eq33 (y : K) : f (y ^ 3) = f y * kk σ y ^ 2 := by
  rcases eq_or_ne (σ y) y with hy | hy
  · have hy3 : σ (y ^ 3) = y ^ 3 := by simp [hy]
    rw [eq_zero_of_fixed h18 hfix hy, eq_zero_of_fixed h18 hfix hy3, zero_mul]
  have hy0 : y ≠ 0 := by rintro rfl; simp at hy
  have hy1 : y - 1 ≠ 0 := by
    intro h; apply hy; rw [show y = 1 by linear_combination h]; simp
  have hy1' : y + 1 ≠ 0 := by
    intro h; apply hy; rw [show y = -1 by linear_combination h]; simp
  have h3 : (3 : K) = 0 := by exact_mod_cast CharP.cast_eq_zero K 3
  have hcube1 : y ^ 3 - 1 = (y - 1) ^ 3 := by linear_combination (y ^ 2 - y) * h3
  have hcube2 : y ^ 3 + 1 = (y + 1) ^ 3 := by linear_combination (-y ^ 2 - y) * h3
  have hy31 : y ^ 3 - 1 ≠ 0 := by rw [hcube1]; exact pow_ne_zero _ hy1
  have hy32 : y ^ 3 + 1 ≠ 0 := by rw [hcube2]; exact pow_ne_zero _ hy1'
  have hw : (y - 1) ^ 2 - 1 ≠ 0 := by
    rw [show (y - 1) ^ 2 - 1 = y * (y - 2) by ring]
    refine mul_ne_zero hy0 fun h => hy1' (by linear_combination h + h3)
  have hy2 : y ^ 2 - 1 ≠ 0 := by
    rw [show y ^ 2 - 1 = (y - 1) * (y + 1) by ring]; exact mul_ne_zero hy1 hy1'
  have hyi : (y ^ 2)⁻¹ - 1 ≠ 0 := by
    rw [show (y ^ 2)⁻¹ - 1 = -(y ^ 2 - 1) / y ^ 2 by field_simp; ring]
    exact div_ne_zero (neg_ne_zero.2 hy2) (pow_ne_zero _ hy0)
  have hpy : pw σ y ≠ 0 := pw_ne_zero hy0
  have hy2' : 1 - y ^ 2 ≠ 0 := fun h => hy2 (by linear_combination -h)
  have hF3 : f (y ^ 3) = f (-y ^ 3) * (y ^ 3 - 1) / (y ^ 3 + 1) := by
    rw [eq_div_iff hy32]; exact eq29 h19 h18 hfix (y ^ 3)
  have hM3 : f (-y ^ 3) = f (y ^ 3 - 1) := by rw [eq26 h19 h18 (y ^ 3 - 1)]; ring_nf
  have hT : f (y ^ 3 - 1) = f (-y) + f (-(y - 1) ^ 2) * pw σ (1 - y)
      - f (-(y ^ 2)⁻¹) * pw σ y ^ 3 := by
    have h := eq25 h19 h18 (y ^ 3 - 1) (-y)
    rw [show (1 : K) + (y ^ 3 - 1) = y ^ 3 by ring, show -y / y ^ 3 = -(y ^ 2)⁻¹ by field_simp,
      pw_pow, show (y ^ 3 - 1) / (1 + -y) = -(y - 1) ^ 2 by
        rw [hcube1, div_eq_iff (by rwa [show (1 : K) + -y = -(y - 1) by ring, neg_ne_zero])]
        ring,
      show (1 : K) + -y = 1 - y by ring] at h
    linear_combination h
  have hSm : f (-(y - 1) ^ 2) = f ((y - 1) ^ 2) * ((y - 1) ^ 2 + 1) / ((y - 1) ^ 2 - 1) := by
    rw [eq_div_iff hw]; exact (eq29 h19 h18 hfix ((y - 1) ^ 2)).symm
  have hS : f ((y - 1) ^ 2) = f (y - 1) * y * (y + σ y - 2) := by
    rw [eq30 h19 h18 hfix hsq (y - 1)]; simp only [map_sub, map_one]; ring_nf
  have hB1 : f (y - 1) = f (-y) := by rw [eq26 h19 h18 (y - 1)]; ring_nf
  have hAm : f (-y) = f y * (y + 1) / (y - 1) := by
    rw [eq_div_iff hy1]; exact (eq29 h19 h18 hfix y).symm
  have hQim : f (-(y ^ 2)⁻¹) = f (y ^ 2)⁻¹ * ((y ^ 2)⁻¹ + 1) / ((y ^ 2)⁻¹ - 1) := by
    rw [eq_div_iff hyi]; exact (eq29 h19 h18 hfix (y ^ 2)⁻¹).symm
  have hQi : f (y ^ 2)⁻¹ = f (y ^ 2) / pw σ y ^ 2 := by
    rw [eq23 h19 h18, pw_pow, div_eq_mul_inv]
  have hQ : f (y ^ 2) = f y * (y + 1) * (y + σ y) := eq30 h19 h18 hfix hsq y
  rw [hF3, hM3, hT, hSm, hS, hB1, hAm, hQim, hQi, hQ]
  simp only [kk, pw, map_sub, map_one]
  have hsy : σ y ≠ 0 := by simpa using hy0
  have hsy1 : 1 - σ y ≠ 0 := by
    intro h; apply hy1; have : σ y = σ 1 := by rw [map_one]; linear_combination -h
    rw [σ.injective this, sub_self]
  field_simp
  rw [← sub_eq_zero]
  ring_nf
  reduce_mod_char!

theorem eq36 (h35 : ∀ x, f (x ^ 3) = f x ^ 3) (x : K) :
    f x = 0 ∨ f x = kk σ x ∨ f x = -kk σ x := by
  have h := eq33 h19 h18 hfix hsq x
  rw [h35] at h
  have : f x * (f x - kk σ x) * (f x + kk σ x) = 0 := by linear_combination h
  rcases mul_eq_zero.1 this with h1 | h1
  · rcases mul_eq_zero.1 h1 with h2 | h2
    · exact Or.inl h2
    · exact Or.inr (Or.inl (by linear_combination h2))
  · exact Or.inr (Or.inr (by linear_combination h1))

theorem final_contra (h35 : ∀ x, f (x ^ 3) = f x ^ 3) {a : K} (ha0 : a ≠ 0) (ha1 : 1 + a ≠ 0)
    (fa : f a = 0) {x0 : K} (hx0 : f x0 = kk σ x0) (hne : f x0 ≠ 0) (hxa : f (x0 / a) = 0) :
    False := by
  have h3 : (3 : K) = 0 := by exact_mod_cast CharP.cast_eq_zero K 3
  have hx01 : 1 + x0 ≠ 0 := by
    intro h; apply hne; rw [show x0 = -1 by linear_combination h]; exact h18.neg_one
  have hxa1 : f (x0 / a - 1) = 0 := eq_zero_sub_one h19 h18 hfix hxa
  have fa1 : f (a - 1) = 0 := eq_zero_sub_one h19 h18 hfix fa
  have E1 : f x0 + f ((a - 1) / (1 + x0)) * pw σ (1 + x0) = 0 := by
    have h := eq25 h19 h18 x0 (a - 1)
    rw [show (1 : K) + (a - 1) = a by ring, fa1, hxa, zero_mul, add_zero] at h
    exact h
  have E2 : f x0 = f ((x0 - a) / (1 + a)) * pw σ (1 + a) := by
    have h := eq24 h19 h18 (x0 - a) a
    have e : f (a / (x0 - a)) * pw σ (x0 - a) = 0 := by
      rw [eq23' h19 h18 a (x0 - a), show (x0 - a) / a = x0 / a - 1 by field_simp, hxa1,
        zero_mul]
    rw [e, show x0 - a + a = x0 by ring, fa] at h
    linear_combination h
  set B := x0 - σ x0 with hB
  set C := a * σ x0 + a - σ a * x0 - σ a with hC
  have hsx01 : 1 + σ x0 ≠ 0 := by
    rw [← map_one σ, ← map_add]; exact (map_ne_zero σ).2 hx01
  have hsa1 : 1 + σ a ≠ 0 := by
    rw [← map_one σ, ← map_add]; exact (map_ne_zero σ).2 ha1
  have id1 : kk σ ((a - 1) / (1 + x0)) * pw σ (1 + x0) = (a + 1 - x0) * (B + C) := by
    simp only [kk, pw, hB, hC, map_div₀, map_sub, map_add, map_one]
    field_simp
    rw [← sub_eq_zero]
    ring_nf
    reduce_mod_char!
  have id2 : kk σ ((x0 - a) / (1 + a)) * pw σ (1 + a) = (x0 + a - 1) * (B - C) := by
    simp only [kk, pw, hB, hC, map_div₀, map_sub, map_add, map_one]
    field_simp
    rw [← sub_eq_zero]
    ring_nf
    reduce_mod_char!
  have hk0 : kk σ x0 = (x0 - 1) * B := rfl
  have hBne : B ≠ 0 := by
    intro h; apply hne; rw [hx0, hk0, h, mul_zero]
  have hx1 : x0 - 1 ≠ 0 := by
    intro h; apply hne; rw [hx0, hk0, h, zero_mul]
  have key : ∀ ε η : K, (ε = 1 ∨ ε = -1) → (η = 1 ∨ η = -1) →
      (x0 - 1) * B + ε * ((a + 1 - x0) * (B + C)) = 0 →
      (x0 - 1) * B = η * ((x0 + a - 1) * (B - C)) → False := by
    intro ε η hε hη e1 e2
    have e3 : B * ((x0 - 1) * (η * (x0 + a - 1) - ε * (a + 1 - x0))
        + 2 * ε * η * (a + 1 - x0) * (x0 + a - 1)) = 0 := by
      linear_combination η * (x0 + a - 1) * e1 - ε * (a + 1 - x0) * e2
    have e4 := (mul_eq_zero.1 e3).resolve_left hBne
    have ha2 : a ^ 2 ≠ 0 := pow_ne_zero 2 ha0
    rcases hε with rfl | rfl <;> rcases hη with rfl | rfl
    · apply ha2
      linear_combination (norm := skip) 2 * e4
      ring_nf
      reduce_mod_char!
    · apply hsq ((1 - x0 - a) / a)
      rw [div_pow, div_eq_iff ha2]
      linear_combination (norm := skip) -e4
      ring_nf
      reduce_mod_char!
    · apply hsq ((1 - x0 + a) / a)
      rw [div_pow, div_eq_iff ha2]
      linear_combination (norm := skip) -e4
      ring_nf
      reduce_mod_char!
    · apply hsq ((1 - x0) / a)
      rw [div_pow, div_eq_iff ha2]
      linear_combination (norm := skip) -e4
      ring_nf
      reduce_mod_char!
  have hw := eq36 h19 h18 hfix hsq h35 ((a - 1) / (1 + x0))
  have hw' := eq36 h19 h18 hfix hsq h35 ((x0 - a) / (1 + a))
  rw [hx0, hk0] at E1 E2 hne
  rcases hw with hw | hw | hw
  · rw [hw, zero_mul, add_zero] at E1; exact hne E1
  all_goals rcases hw' with hw' | hw' | hw'
  all_goals try (rw [hw', zero_mul] at E2; exact hne E2)
  · exact key 1 1 (Or.inl rfl) (Or.inl rfl) (by rw [hw, id1] at E1; linear_combination E1)
      (by rw [hw', id2] at E2; linear_combination E2)
  · exact key 1 (-1) (Or.inl rfl) (Or.inr rfl) (by rw [hw, id1] at E1; linear_combination E1)
      (by rw [hw', neg_mul, id2] at E2; linear_combination E2)
  · exact key (-1) 1 (Or.inr rfl) (Or.inl rfl)
      (by rw [hw, neg_mul, id1] at E1; linear_combination E1)
      (by rw [hw', id2] at E2; linear_combination E2)
  · exact key (-1) (-1) (Or.inr rfl) (Or.inr rfl)
      (by rw [hw, neg_mul, id1] at E1; linear_combination E1)
      (by rw [hw', neg_mul, id2] at E2; linear_combination E2)

end Three

end Derived

section Linear

variable {σ : K ≃+* K}

theorem eq19_lin {f g : K → K} (hf : Eq19 σ f) (hg : Eq19 σ g) (c d : K) :
    Eq19 σ (fun x => c * f x - d * g x) := fun x y => by
  linear_combination c * hf x y - d * hg x y

theorem norm18_lin {f g : K → K} (hf : Norm18 f) (hg : Norm18 g) (c d : K) :
    Norm18 (fun x => c * f x - d * g x) :=
  ⟨by simp [hf.zero, hg.zero], by simp [hf.one, hg.one], by simp [hf.neg_one, hg.neg_one]⟩

theorem eq19_neg {f : K → K} (hf : Eq19 σ f) : Eq19 σ (fun x => -f x) := fun x y => by
  linear_combination -hf x y

theorem norm18_neg {f : K → K} (hf : Norm18 f) : Norm18 (fun x => -f x) :=
  ⟨by simp [hf.zero], by simp [hf.one], by simp [hf.neg_one]⟩

end Linear

section Twist

variable [CharP K 3] [Fact (Nat.Prime 3)] [Finite K]

noncomputable def twist (f : K → K) (x : K) : K := (frobeniusEquiv K 3).symm (f (x ^ 3))

variable {σ : K ≃+* K}

theorem twist_cube (f : K → K) (x : K) : twist f x ^ 3 = f (x ^ 3) :=
  frobeniusEquiv_symm_pow_p K 3 _

theorem twist_eq_zero {f : K → K} {x : K} : twist f x = 0 ↔ f (x ^ 3) = 0 := by
  rw [twist, map_eq_zero_iff _ (frobeniusEquiv K 3).symm.injective]

theorem twist_eq19 {f : K → K} (hf : Eq19 σ f) : Eq19 σ (twist f) := fun x y => by
  rw [← pow_eq_zero_iff (n := 3) (by norm_num), sub_pow_char, sub_pow_char, add_pow_char,
    mul_pow, mul_pow, twist_cube, twist_cube, twist_cube, twist_cube, ← pw_pow, ← pw_pow,
    div_pow, div_pow, add_pow_char, add_pow_char, one_pow]
  exact hf (x ^ 3) (y ^ 3)

theorem twist_norm18 {f : K → K} (hf : Norm18 f) : Norm18 (twist f) := by
  refine ⟨twist_eq_zero.2 ?_, twist_eq_zero.2 ?_, twist_eq_zero.2 ?_⟩
  · simpa using hf.zero
  · simpa using hf.one
  · simpa [Odd.neg_one_pow (by decide : Odd 3)] using hf.neg_one

theorem twist_eq_zero_iff (hfix : ∀ x : K, σ x = x → x = 0 ∨ x = 1 ∨ x = -1)
    (hsq : ∀ x : K, x ^ 2 ≠ -1) {f : K → K} (h19 : Eq19 σ f) (h18 : Norm18 f) (z : K) :
    twist f z = 0 ↔ f z = 0 := by
  rw [twist_eq_zero, eq33 h19 h18 hfix hsq z, mul_eq_zero]
  refine ⟨fun h => h.elim id fun h => ?_, fun h => Or.inl h⟩
  rw [kk, pow_eq_zero_iff (by norm_num), mul_eq_zero] at h
  rcases h with h | h
  · rw [show z = 1 by linear_combination h]; exact h18.one
  · exact eq_zero_of_fixed h18 hfix (by linear_combination -h)

end Twist

section Family

variable [CharP K 3] {σ : K ≃+* K} (hfix : ∀ x : K, σ x = x → x = 0 ∨ x = 1 ∨ x = -1)
  (hsq : ∀ x : K, x ^ 2 ≠ -1) {a : K} (ha0 : a ≠ 0) (ha1 : 1 + a ≠ 0)
include hfix hsq ha0 ha1

theorem eq_zero_of_eq35 (hgen : ∀ x ≠ 0, ∃ i : ℕ, a ^ i = x) {f : K → K} (h19 : Eq19 σ f)
    (h18 : Norm18 f) (fa : f a = 0) (h35 : ∀ x, f (x ^ 3) = f x ^ 3) : f = 0 := by
  by_contra hf
  have hx : ∃ x0, f x0 ≠ 0 ∧ f (x0 / a) = 0 := by
    by_contra hno
    push Not at hno
    apply hf
    have hpow : ∀ i : ℕ, f (a ^ i) = 0 := by
      intro i
      induction i with
      | zero => simpa using h18.one
      | succ i ih =>
        by_contra h
        exact hno _ h (by rwa [pow_succ, mul_div_assoc, div_self ha0, mul_one])
    funext x
    rcases eq_or_ne x 0 with rfl | hx
    · exact h18.zero
    · obtain ⟨i, rfl⟩ := hgen x hx
      exact hpow i
  obtain ⟨x0, hx0, hxa⟩ := hx
  rcases eq36 h19 h18 hfix hsq h35 x0 with h | h | h
  · exact hx0 h
  · exact final_contra h19 h18 hfix hsq h35 ha0 ha1 fa h hx0 hxa
  · refine final_contra (f := fun x => -f x) (eq19_neg h19) (norm18_neg h18) hfix hsq
      (fun x => by show -f (x ^ 3) = (-f x) ^ 3; rw [h35]; ring) ha0 ha1
      (by show -f a = 0; rw [fa, neg_zero]) (by show -f x0 = kk σ x0; rw [h, neg_neg])
      (by show -f x0 ≠ 0; exact neg_ne_zero.2 hx0) (by show -f (x0 / a) = 0; rw [hxa, neg_zero])

theorem eq_zero_of_eq34 [Finite K] (hgen : ∀ x ≠ 0, ∃ i : ℕ, a ^ i = x) {f : K → K}
    (h19 : Eq19 σ f) (h18 : Norm18 f) (fa : f a = 0) (b : K)
    (h34 : ∀ x, f (x ^ 3) = (b * f x) ^ 3) : f = 0 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_contra hf
  obtain ⟨x1, hx1⟩ := Function.ne_iff.1 hf
  replace hx1 : f x1 ≠ 0 := hx1
  have hb : b ≠ 0 := by
    rintro rfl
    apply hx1
    have h3 := h34 ((frobeniusEquiv K 3).symm x1)
    rwa [frobeniusEquiv_symm_pow_p, zero_mul, zero_pow (by norm_num)] at h3
  have e33 := eq33 h19 h18 hfix hsq x1
  rw [h34] at e33
  set e := kk σ x1 / f x1 with he
  have he2 : e ^ 2 = b ^ 3 := by
    rw [he, div_pow, div_eq_iff (pow_ne_zero 2 hx1)]
    have : f x1 * (b ^ 3 * f x1 ^ 2 - kk σ x1 ^ 2) = 0 := by linear_combination e33
    linear_combination -((mul_eq_zero.1 this).resolve_left hx1)
  have he0 : e ≠ 0 := by
    intro h; rw [h, zero_pow (by norm_num)] at he2; exact pow_ne_zero 3 hb he2.symm
  have key := eq_zero_of_eq35 hfix hsq ha0 ha1 hgen (f := fun x => e * f x - 0 * f x)
    (eq19_lin h19 h19 e 0) (norm18_lin h18 h18 e 0)
    (by simp [fa]) (fun x => by
      simp only [zero_mul, sub_zero, h34]
      linear_combination -(f x) ^ 3 * e * he2)
  have := congrFun key x1
  simp only [zero_mul, sub_zero, Pi.zero_apply, mul_eq_zero] at this
  rcases this with h | h
  · exact he0 h
  · exact hx1 h

theorem funEq_eq_zero [Fact (Nat.Prime 3)] [Fintype K] (hgen : ∀ x ≠ 0, ∃ i : ℕ, a ^ i = x)
    {f : K → K} (h19 : Eq19 σ f) (h18 : Norm18 f) (fa : f a = 0) : f = 0 := by
  set q := Fintype.card K with hq
  have haq : a ^ (q - 1) = 1 := FiniteField.pow_card_sub_one_eq_one a ha0
  let Pr : ℕ → Prop := fun r => ∀ g : K → K, Eq19 σ g → Norm18 g → g a = 0 →
    (∀ s, 1 ≤ s → s ≤ r → g (a ^ s) = 0) → g = 0
  have base : Pr (q - 1) := by
    intro g _ hg18 _ hvan
    funext x
    rcases eq_or_ne x 0 with rfl | hx
    · exact hg18.zero
    obtain ⟨i, rfl⟩ := hgen x hx
    have hq1 : 0 < q - 1 := by
      have : 1 < q := Fintype.one_lt_card
      omega
    rcases Nat.eq_zero_or_pos (i % (q - 1)) with h0 | hpos
    · have : a ^ i = a ^ (q - 1) := by
        rw [← Nat.div_add_mod i (q - 1), h0, add_zero, pow_mul, haq, one_pow]
      rw [this]
      exact hvan _ hq1 le_rfl
    · have : a ^ i = a ^ (i % (q - 1)) := by
        conv_lhs => rw [← Nat.div_add_mod i (q - 1), pow_add, pow_mul, haq, one_pow, one_mul]
      rw [this]
      exact hvan _ hpos (Nat.mod_lt _ hq1).le
  have step : ∀ r, Pr (r + 1) → Pr r := by
    intro r IH g hg19 hg18 hga hvan
    by_cases hr : g (a ^ (r + 1)) = 0
    · refine IH g hg19 hg18 hga fun s hs1 hs2 => ?_
      rcases Nat.lt_or_ge s (r + 1) with h | h
      · exact hvan s hs1 (by omega)
      · rwa [show s = r + 1 by omega]
    set c := g (a ^ (r + 1))
    set d := twist g (a ^ (r + 1))
    have hd : d ≠ 0 := fun h => hr ((twist_eq_zero_iff hfix hsq hg19 hg18 _).1 h)
    have hh := IH (fun x => c * twist g x - d * g x)
      (eq19_lin (twist_eq19 hg19) hg19 c d)
      (norm18_lin (twist_norm18 hg18) hg18 c d)
      (by simp [hga, (twist_eq_zero_iff hfix hsq hg19 hg18 a).2 hga])
      (fun s hs1 hs2 => by
        rcases Nat.lt_or_ge s (r + 1) with h | h
        · have h0 := hvan s hs1 (by omega)
          simp [h0, (twist_eq_zero_iff hfix hsq hg19 hg18 _).2 h0]
        · rw [show s = r + 1 by omega]
          ring)
    refine eq_zero_of_eq34 hfix hsq ha0 ha1 hgen hg19 hg18 hga (d / c) fun x => ?_
    have hx := congrFun hh x
    simp only [Pi.zero_apply] at hx
    have : twist g x = d / c * g x := by
      field_simp
      linear_combination hx
    rw [← twist_cube g x, this]
  have hall : ∀ k, Pr (q - 1 - k) := by
    intro k
    induction k with
    | zero => simpa using base
    | succ k ih =>
      rcases Nat.lt_or_ge k (q - 1) with h | h
      · exact step _ (by rwa [show q - 1 - (k + 1) + 1 = q - 1 - k by omega])
      · rwa [show q - 1 - (k + 1) = q - 1 - k by omega]
  exact hall (q - 1) f h19 h18 fa fun s hs1 hs2 => by omega

end Family

end CFSG.Walter.Ree.Thompson1
