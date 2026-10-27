module

public import CFSG.Quasithin.Vol2.Ch10SecB3Obl

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB

theorem factFieldAutQuot_holds :
    ∀ (F : Type) [Field F] [Finite F] (σ : F ≃+* F), σ ≠ RingEquiv.refl F →
      ∃ l : F, l ≠ 0 ∧ σ (σ l / l) ≠ σ l / l := by
  intro F _ _ σ hσ
  by_contra! h
  refine hσ (RingEquiv.ext fun x => ?_)
  rw [RingEquiv.refl_apply]
  by_contra hx
  have hx0 : x ≠ 0 := by
    rintro rfl
    exact hx (map_zero σ)
  have hx1 : x + 1 ≠ 0 := by
    intro h1
    have : x = -1 := eq_neg_of_add_eq_zero_left h1
    exact hx (by rw [this, map_neg, map_one])
  have hfa : σ (σ x / x) = σ x / x := h x hx0
  have hfb : σ (σ (x + 1) / (x + 1)) = σ (x + 1) / (x + 1) := h (x + 1) hx1
  set a := σ x / x with ha
  set b := σ (x + 1) / (x + 1) with hb
  have hax : σ x = a * x := by rw [ha, div_mul_cancel₀ _ hx0]
  have hbx : σ x + 1 = b * (x + 1) := by
    rw [hb, div_mul_cancel₀ _ hx1, map_add, map_one]
  have hlin : (a - b) * x = b - 1 := by linear_combination hbx - hax
  by_cases hab : a = b
  · have hb1 : b = 1 := by
      rw [hab, sub_self, zero_mul] at hlin
      linear_combination -hlin
    exact hx (by rw [hax, hab, hb1, one_mul])
  · have hsub : a - b ≠ 0 := sub_ne_zero.mpr hab
    have hxe : x = (b - 1) / (a - b) := by
      rw [eq_div_iff hsub, mul_comm]
      exact hlin
    exact hx (by rw [hxe, map_div₀, map_sub, map_sub, map_one, hfa, hfb])

end CFSG.Quasithin.Vol2.Ch10.SecB
