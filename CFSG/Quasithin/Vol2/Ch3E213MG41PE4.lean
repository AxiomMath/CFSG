module

public import CFSG.Quasithin.Vol2.Ch3E213MG41PE3
public import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.Quasithin.Ch3E213M.G41.Big.IPL

variable {k : Type} [Field k] [CharP k 2]

theorem conic_line_eq {c A B κ κ' : k} {u : k × k} (hq : qC c u = κ)
    (hl : A * u.1 + B * u.2 = κ') :
    (A ^ 2 + B ^ 2 + c * A * B) * u.2 ^ 2 + c * A * κ' * u.2 + (κ' ^ 2 + κ * A ^ 2) = 0 := by
  have h0 : (2 : k) = 0 := CharTwo.two_eq_zero
  simp only [qC] at hq
  linear_combination (-(c * A * u.2 + κ' + A * u.1 + B * u.2)) * hl - A ^ 2 * hq +
    (A * B * c * u.2 ^ 2 + A ^ 2 * c * u.1 * u.2 + A * B * u.1 * u.2 + A ^ 2 * u.1 ^ 2 +
      A ^ 2 * u.2 ^ 2 + B ^ 2 * u.2 ^ 2) * h0

omit [CharP k 2] in
theorem eq_of_line {A B κ' : k} (hA : A ≠ 0) {u v : k × k} (hu : A * u.1 + B * u.2 = κ')
    (hv : A * v.1 + B * v.2 = κ') (h2 : u.2 = v.2) : u = v :=
  Prod.ext (mul_left_cancel₀ hA (by linear_combination hu - hv - B * h2)) h2

theorem conic_line_of_ne {c A B κ κ' : k} (hc : c ≠ 0) (hA : A ≠ 0) (hκ : κ ≠ 0)
    {u₁ u₂ u₃ : k × k} (h₁₂ : u₁ ≠ u₂) (h₁₃ : u₁ ≠ u₃) (h₂₃ : u₂ ≠ u₃) (hq₁ : qC c u₁ = κ)
    (hq₂ : qC c u₂ = κ) (hq₃ : qC c u₃ = κ) (hl₁ : A * u₁.1 + B * u₁.2 = κ')
    (hl₂ : A * u₂.1 + B * u₂.2 = κ') (hl₃ : A * u₃.1 + B * u₃.2 = κ') : False := by
  have E₁ := conic_line_eq hq₁ hl₁
  have E₂ := conic_line_eq hq₂ hl₂
  have E₃ := conic_line_eq hq₃ hl₃
  have d₁₂ : u₁.2 - u₂.2 ≠ 0 := sub_ne_zero.mpr fun h => h₁₂ (eq_of_line hA hl₁ hl₂ h)
  have d₁₃ : u₁.2 - u₃.2 ≠ 0 := sub_ne_zero.mpr fun h => h₁₃ (eq_of_line hA hl₁ hl₃ h)
  have d₂₃ : u₂.2 - u₃.2 ≠ 0 := sub_ne_zero.mpr fun h => h₂₃ (eq_of_line hA hl₂ hl₃ h)
  have e₁₂ : (A ^ 2 + B ^ 2 + c * A * B) * (u₁.2 + u₂.2) + c * A * κ' = 0 :=
    mul_left_cancel₀ d₁₂ (by linear_combination E₁ - E₂)
  have e₁₃ : (A ^ 2 + B ^ 2 + c * A * B) * (u₁.2 + u₃.2) + c * A * κ' = 0 :=
    mul_left_cancel₀ d₁₃ (by linear_combination E₁ - E₃)
  have ha : A ^ 2 + B ^ 2 + c * A * B = 0 :=
    mul_left_cancel₀ d₂₃ (by linear_combination e₁₂ - e₁₃)
  have hκ' : κ' = 0 := by
    have h : c * A * κ' = 0 := by linear_combination e₁₂ - (u₁.2 + u₂.2) * ha
    simpa [hc, hA] using h
  have h : κ * A ^ 2 = 0 := by
    linear_combination E₁ - u₁.2 ^ 2 * ha - (c * A * u₁.2 + κ') * hκ'
  exact hκ (by simpa [hA] using h)

theorem conic_line_zero_of_ne {c A B κ : k} (hA : A ≠ 0) (hκ : κ ≠ 0) {u₁ u₂ : k × k}
    (h₁₂ : u₁ ≠ u₂) (hq₁ : qC c u₁ = κ) (hq₂ : qC c u₂ = κ) (hl₁ : A * u₁.1 + B * u₁.2 = 0)
    (hl₂ : A * u₂.1 + B * u₂.2 = 0) : False := by
  have h0 : (2 : k) = 0 := CharTwo.two_eq_zero
  have E₁ := conic_line_eq hq₁ hl₁
  have E₂ := conic_line_eq hq₂ hl₂
  have d : (u₁.2 - u₂.2) ^ 2 ≠ 0 :=
    pow_ne_zero 2 (sub_ne_zero.mpr fun h => h₁₂ (eq_of_line hA hl₁ hl₂ h))
  have ha : A ^ 2 + B ^ 2 + c * A * B = 0 := by
    refine mul_left_cancel₀ d ?_
    linear_combination E₁ - E₂ + (A ^ 2 + B ^ 2 + c * A * B) * (u₂.2 ^ 2 - u₁.2 * u₂.2) * h0
  have h : κ * A ^ 2 = 0 := by linear_combination E₁ - u₁.2 ^ 2 * ha
  exact hκ (by simpa [hA] using h)

omit [CharP k 2] in
theorem qC_swap (c : k) (u : k × k) : qC c u.swap = qC c u := by
  simp only [qC, Prod.fst_swap, Prod.snd_swap]
  ring

theorem conic_line {c A B κ κ' : k} (hc : c ≠ 0) (hAB : A ≠ 0 ∨ B ≠ 0) (hκ : κ ≠ 0)
    {u₁ u₂ u₃ : k × k} (h₁₂ : u₁ ≠ u₂) (h₁₃ : u₁ ≠ u₃) (h₂₃ : u₂ ≠ u₃) (hq₁ : qC c u₁ = κ)
    (hq₂ : qC c u₂ = κ) (hq₃ : qC c u₃ = κ) (hl₁ : A * u₁.1 + B * u₁.2 = κ')
    (hl₂ : A * u₂.1 + B * u₂.2 = κ') (hl₃ : A * u₃.1 + B * u₃.2 = κ') : False := by
  rcases hAB with hA | hB
  · exact conic_line_of_ne hc hA hκ h₁₂ h₁₃ h₂₃ hq₁ hq₂ hq₃ hl₁ hl₂ hl₃
  · have hs : ∀ u : k × k, A * u.1 + B * u.2 = κ' → B * u.swap.1 + A * u.swap.2 = κ' :=
      fun u hu => by simp only [Prod.fst_swap, Prod.snd_swap]; linear_combination hu
    exact conic_line_of_ne hc hB hκ (u₁ := u₁.swap) (u₂ := u₂.swap) (u₃ := u₃.swap)
      (fun h => h₁₂ (Prod.swap_injective h)) (fun h => h₁₃ (Prod.swap_injective h))
      (fun h => h₂₃ (Prod.swap_injective h)) (by rw [qC_swap, hq₁]) (by rw [qC_swap, hq₂])
      (by rw [qC_swap, hq₃]) (hs _ hl₁) (hs _ hl₂) (hs _ hl₃)

theorem conic_line_zero {c A B κ : k} (hAB : A ≠ 0 ∨ B ≠ 0) (hκ : κ ≠ 0) {u₁ u₂ : k × k}
    (h₁₂ : u₁ ≠ u₂) (hq₁ : qC c u₁ = κ) (hq₂ : qC c u₂ = κ) (hl₁ : A * u₁.1 + B * u₁.2 = 0)
    (hl₂ : A * u₂.1 + B * u₂.2 = 0) : False := by
  rcases hAB with hA | hB
  · exact conic_line_zero_of_ne hA hκ h₁₂ hq₁ hq₂ hl₁ hl₂
  · have hs : ∀ u : k × k, A * u.1 + B * u.2 = 0 → B * u.swap.1 + A * u.swap.2 = 0 :=
      fun u hu => by simp only [Prod.fst_swap, Prod.snd_swap]; linear_combination hu
    exact conic_line_zero_of_ne hB hκ (u₁ := u₁.swap) (u₂ := u₂.swap)
      (fun h => h₁₂ (Prod.swap_injective h)) (by rw [qC_swap, hq₁]) (by rw [qC_swap, hq₂])
      (hs _ hl₁) (hs _ hl₂)

theorem orbit_line {c : k} (hc0 : c ≠ 0) (hc1 : c ≠ 1) {v : k × k} (hv : qC c v ≠ 0)
    {A B : k} (hAB : A ≠ 0 ∨ B ≠ 0) (κ' : k) (i j l : ℕ) (hi : i < 5) (hj : j < 5) (hl : l < 5)
    (h₁ : A * ((rotC c)^[i] v).1 + B * ((rotC c)^[i] v).2 = κ')
    (h₂ : A * ((rotC c)^[j] v).1 + B * ((rotC c)^[j] v).2 = κ')
    (h₃ : A * ((rotC c)^[l] v).1 + B * ((rotC c)^[l] v).2 = κ') : i = j ∨ i = l ∨ j = l := by
  by_contra h
  simp only [not_or] at h
  exact conic_line hc0 hAB hv (fun e => h.1 (iterate_rotC_inj hc0 hc1 hv hi hj e))
    (fun e => h.2.1 (iterate_rotC_inj hc0 hc1 hv hi hl e))
    (fun e => h.2.2 (iterate_rotC_inj hc0 hc1 hv hj hl e)) (qC_iterate c v i)
    (qC_iterate c v j) (qC_iterate c v l) h₁ h₂ h₃

theorem orbit_line_zero {c : k} (hc0 : c ≠ 0) (hc1 : c ≠ 1) {v : k × k} (hv : qC c v ≠ 0)
    {A B : k} (hAB : A ≠ 0 ∨ B ≠ 0) (i j : ℕ) (hi : i < 5) (hj : j < 5)
    (h₁ : A * ((rotC c)^[i] v).1 + B * ((rotC c)^[i] v).2 = 0)
    (h₂ : A * ((rotC c)^[j] v).1 + B * ((rotC c)^[j] v).2 = 0) : i = j := by
  by_contra h
  exact conic_line_zero hAB hv (fun e => h (iterate_rotC_inj hc0 hc1 hv hi hj e))
    (qC_iterate c v i) (qC_iterate c v j) h₁ h₂

end CFSG.Quasithin.Ch3E213M.G41.Big.IPL
