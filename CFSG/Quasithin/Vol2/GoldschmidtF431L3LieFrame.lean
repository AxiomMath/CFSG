module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_7FinMaxL3
public import CFSG.Quasithin.Vol2.GoldschmidtF431L3Datum

public section

namespace CFSG.Quasithin.H13.F431.L3.P3

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Open CFSG.QuasithinUnique.Fin257
  CFSG.QuasithinUnique.Fin257.L3 CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.LocalAnalysis.ComponentInitial.LinearFieldFour

variable {F : Type} [Field F] [CharP F 2]

theorem U_mul (c a b c' a' b' : F) :
    (wP c * xP a * yP b) * (wP c' * xP a' * yP b') =
      wP (c + c' + a' * b) * xP (a + a') * yP (b + b') := by
  have h1 : yP b * wP c' = wP c' * yP b := (wP_mul_yP c' b).symm
  have h2 : xP a * wP c' = wP c' * xP a := (wP_mul_xP c' a).symm
  have h3 : yP b * xP a' = wP (a' * b) * xP a' * yP b := yP_mul_xP a' b
  have h4 : xP a * wP (a' * b) = wP (a' * b) * xP a := (wP_mul_xP _ a).symm
  rw [wP_add, wP_add, xP_add, yP_add]
  calc wP c * xP a * yP b * (wP c' * xP a' * yP b')
      = wP c * xP a * (yP b * wP c') * xP a' * yP b' := by group
    _ = wP c * xP a * (wP c' * yP b) * xP a' * yP b' := by rw [h1]
    _ = wP c * (xP a * wP c') * yP b * xP a' * yP b' := by group
    _ = wP c * (wP c' * xP a) * yP b * xP a' * yP b' := by rw [h2]
    _ = wP c * wP c' * xP a * (yP b * xP a') * yP b' := by group
    _ = wP c * wP c' * xP a * (wP (a' * b) * xP a' * yP b) * yP b' := by rw [h3]
    _ = wP c * wP c' * (xP a * wP (a' * b)) * xP a' * yP b * yP b' := by group
    _ = wP c * wP c' * (wP (a' * b) * xP a) * xP a' * yP b * yP b' := by rw [h4]
    _ = wP c * wP c' * wP (a' * b) * (xP a * xP a') * (yP b * yP b') := by group

theorem U_comm (c a b c' a' b' : F) :
    (wP c * xP a * yP b) * (wP c' * xP a' * yP b') =
      wP (a' * b + a * b') * ((wP c' * xP a' * yP b') * (wP c * xP a * yP b)) := by
  rw [U_mul, U_mul]
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have e : (a' * b + a * b') + (c + c' + a * b') = c + c' + a' * b := by
    linear_combination (a * b') * h2
  rw [show c' + c = c + c' from add_comm _ _, show a' + a = a + a' from add_comm _ _,
    show b' + b = b + b' from add_comm _ _, ← mul_assoc, ← mul_assoc, ← wP_add]
  rw [e]

theorem wP_mem_U (c : F) : wP c ∈ projUnitriangular 3 F :=
  mem_Ubar.mpr ⟨c, 0, 0, by rw [xP_zero, yP_zero, mul_one, mul_one]⟩

theorem eq_zero_of_comm {c a b c' a' b' : F}
    (h : (wP c * xP a * yP b) * (wP c' * xP a' * yP b') =
      (wP c' * xP a' * yP b') * (wP c * xP a * yP b)) : a' * b + a * b' = 0 := by
  rw [U_comm] at h
  have h1 : wP (a' * b + a * b') = 1 := by
    have h2 : wP (a' * b + a * b') * ((wP c' * xP a' * yP b') * (wP c * xP a * yP b)) =
        1 * ((wP c' * xP a' * yP b') * (wP c * xP a * yP b)) := by rw [one_mul]; exact h
    exact mul_right_cancel h2
  exact (wP_eq_one_iff _).mp h1

theorem centerOf_U :
    centerOf (projUnitriangular 3 F) = (Wg : Subgroup (projectiveSL 3 F)) := by
  apply le_antisymm
  · rintro u ⟨huU, hc⟩
    replace hc := Subgroup.mem_centralizer_iff.mp hc
    obtain ⟨c, a, b, rfl⟩ := mem_Ubar.mp huU
    have h1 := hc (wP 0 * xP 1 * yP 0) (mem_Ubar.mpr ⟨0, 1, 0, rfl⟩)
    have h2 := hc (wP 0 * xP 0 * yP 1) (mem_Ubar.mpr ⟨0, 0, 1, rfl⟩)
    have e1 := eq_zero_of_comm h1.symm
    have e2 := eq_zero_of_comm h2.symm
    have hb : b = 0 := by simpa using e1
    have ha : a = 0 := by simpa using e2
    subst ha; subst hb
    exact ⟨c, by rw [xP_zero, yP_zero, mul_one, mul_one]⟩
  · rintro _ ⟨c, rfl⟩
    refine ⟨wP_mem_U c, Subgroup.mem_centralizer_iff.mpr ?_⟩
    intro h hh
    obtain ⟨c', a', b', rfl⟩ := mem_Ubar.mp hh
    have := U_comm c' a' b' c 0 0
    simp only [mul_zero, zero_mul, add_zero, wP_zero, one_mul] at this
    have e : wP c = wP c * xP 0 * yP 0 := by rw [xP_zero, yP_zero, mul_one, mul_one]
    rw [e]
    exact this

theorem frame_U [Finite F] :
    Frame (projUnitriangular 3 F) (V1 : Subgroup (projectiveSL 3 F)) V2 where
  Q₁_le := V1_le_U
  Q₂_le := V2_le_U
  Q₁_ea := isElemAbelian_V1
  Q₂_ea := isElemAbelian_V2
  inter := by rw [V1_inf_V2, centerOf_U]
  card_eq := card_V1_eq_card_V2
  four_le := by
    rw [card_V1]
    have : 2 ≤ Nat.card F := Nat.succ_le_of_lt Finite.one_lt_card
    nlinarith
  Q_ne := V1_ne_V2
  comm := by
    intro x hx y hy
    obtain ⟨c, a, b, rfl⟩ := mem_Ubar.mp hx
    obtain ⟨c', a', b', rfl⟩ := mem_Ubar.mp hy
    rw [centerOf_U]
    refine ⟨a' * b + a * b', ?_⟩
    have := U_comm c a b c' a' b'
    calc wP c * xP a * yP b * (wP c' * xP a' * yP b') * (wP c * xP a * yP b)⁻¹ *
          (wP c' * xP a' * yP b')⁻¹
        = wP (a' * b + a * b') * ((wP c' * xP a' * yP b') * (wP c * xP a * yP b)) *
          (wP c * xP a * yP b)⁻¹ * (wP c' * xP a' * yP b')⁻¹ := by rw [this]
      _ = wP (a' * b + a * b') := by group
  inv := fun x hx hx2 _ => mem_V1_or_V2_of_sq hx (by rw [← pow_two]; exact hx2)
  cent₁ := by
    intro x hx hxZ y hy hyx
    obtain ⟨a, c, rfl⟩ := mem_V1.mp hx
    obtain ⟨c', a', b', rfl⟩ := mem_Ubar.mp hy
    have hxe : xP a * wP c = wP c * xP a * yP 0 := by rw [yP_zero, mul_one, wP_mul_xP]
    have ha : a ≠ 0 := by
      rintro rfl
      apply hxZ
      rw [centerOf_U]
      exact ⟨c, by rw [xP_zero, one_mul]⟩
    rw [hxe] at hyx
    have h0 := eq_zero_of_comm hyx.symm
    have hb : b' = 0 := by
      have : a * b' = 0 := by simpa using h0
      exact (mul_eq_zero.mp this).resolve_left ha
    subst hb
    exact ⟨a', c', by rw [yP_zero, mul_one, wP_mul_xP]⟩
  cent₂ := by
    intro x hx hxZ y hy hyx
    obtain ⟨b, c, rfl⟩ := mem_V2.mp hx
    obtain ⟨c', a', b', rfl⟩ := mem_Ubar.mp hy
    have hxe : yP b * wP c = wP c * xP 0 * yP b := by rw [xP_zero, mul_one, wP_mul_yP]
    have hb : b ≠ 0 := by
      rintro rfl
      apply hxZ
      rw [centerOf_U]
      exact ⟨c, by rw [yP_zero, one_mul]⟩
    rw [hxe] at hyx
    have h0 := eq_zero_of_comm hyx.symm
    have ha : a' = 0 := by
      have : a' * b = 0 := by simpa using h0
      exact (mul_eq_zero.mp this).resolve_right hb
    subst ha
    exact ⟨b', c', by rw [xP_zero, mul_one, wP_mul_yP]⟩
  maxea := by
    intro A hA hAe hcard
    have hsq : ∀ x ∈ A, x * x = 1 := fun x hx => by
      rw [← pow_two]; exact F7.isElemAbelian_pow_eq_one hAe hx
    rcases elem_le_V1_or_V2 hA hsq with h | h
    · exact Or.inl (Subgroup.eq_of_le_of_card_ge h hcard)
    · refine Or.inr (Subgroup.eq_of_le_of_card_ge h ?_)
      rw [← card_V1_eq_card_V2]
      exact hcard

end CFSG.Quasithin.H13.F431.L3.P3
