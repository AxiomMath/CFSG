module

public import CFSG.Quasithin.EmptyFaithful.S146zNAmtE
public import CFSG.Quasithin.EmptyFaithful.S146zNAmtDef

public section

namespace CFSG.Quasithin.A6Amt

section Quadratic

variable {V : Type} [CommGroup V] [Finite V] {Γ L : Subgroup (MulAut V)} {W₁ W₂ : Subgroup V}
  {s : MulAut V}

omit [Finite V] in
theorem quad_apply {A : Subgroup (MulAut V)} (hq : commSeries A 2 = ⊥) {a b : MulAut V}
    (ha : a ∈ A) (hb : b ∈ A) (w : V) : a (b w * w⁻¹) = b w * w⁻¹ := by
  have hQ : commV A ≤ fixV A := (isQuadratic_iff_commSeries_two A).mpr hq
  exact hQ (Subgroup.subset_closure ⟨b, hb, w, rfl⟩) a ha

theorem Ctx.A_le_stab (c : Ctx Γ L W₁ W₂ s) (F : A6Facts c.rL c.cL) {A : Subgroup (MulAut V)}
    (hA : A ≤ Γ) (hsq : ∀ a ∈ A, a ^ 2 = 1) (hq : commSeries A 2 = ⊥) (hcard : 4 ≤ Nat.card A) :
    A ≤ stabSub W₁ := by
  intro f hfA
  by_contra hf
  obtain ⟨hf1, hf2⟩ := c.swap_of_not_stab F (hA hfA) hf
  obtain ⟨a, haA, ha1, haf⟩ : ∃ a ∈ A, a ≠ 1 ∧ a ≠ f := by
    obtain ⟨a, b, hab, ha1, hb1⟩ := exists_two_ne_one (G := ↥A) hcard
    by_cases hfa : (a : MulAut V) = f
    · exact ⟨b, b.2, fun h => hb1 (Subtype.ext h), fun h => hab (Subtype.ext (hfa.trans h.symm))⟩
    · exact ⟨a, a.2, fun h => ha1 (Subtype.ext h), hfa⟩
  obtain ⟨a', ha'A, ha'1, ha'st⟩ : ∃ a' ∈ A, a' ≠ 1 ∧ a' ∈ stabSub W₁ := by
    by_cases hast : a ∈ stabSub W₁
    · exact ⟨a, haA, ha1, hast⟩
    · have hff : f * f = 1 := by rw [← pow_two]; exact hsq f hfA
      refine ⟨f * a, A.mul_mem hfA haA, fun h => haf ?_, fun u => ?_⟩
      · exact (eq_inv_of_mul_eq_one_right h).trans (inv_eq_of_mul_eq_one_right hff)
      · have := (c.swap_of_not_stab F (hA haA) hast).1
        show f (a u) ∈ W₁ ↔ u ∈ W₁
        rw [hf2 (a u), this u]
  have ha'Γ := hA ha'A
  have ha'W₂ := c.stab₂ F ha'Γ ha'st
  have hfix : ∀ w ∈ W₁, a' w = w := by
    intro w hw
    have hq' := quad_apply hq ha'A hfA w
    rw [map_mul, map_inv] at hq'
    have hfw : f w ∈ W₂ := (hf1 w).2 hw
    have hx : a' (f w) * (f w)⁻¹ ∈ W₂ := W₂.mul_mem ((ha'W₂ _).2 hfw) (W₂.inv_mem hfw)
    have hy : a' w * w⁻¹ ∈ W₁ := W₁.mul_mem ((ha'st w).2 hw) (W₁.inv_mem hw)
    have h1 : a' (f w) / a' w = f w / w := by simpa [div_eq_mul_inv] using hq'
    have h2 := div_eq_div_iff_mul_eq_mul.mp h1
    have h3 : a' w / w = a' (f w) / f w := by
      rw [div_eq_div_iff_mul_eq_mul]
      exact (h2.trans (mul_comm _ _)).symm
    have h4 : a' w * w⁻¹ ∈ W₁ ⊓ W₂ := ⟨hy, by
      rw [← div_eq_mul_inv, h3, div_eq_mul_inv]; exact hx⟩
    rw [c.inf_eq_bot F, Subgroup.mem_bot, mul_inv_eq_one] at h4
    exact h4
  exact ha'1 (c.eq_one_of_res F ha'Γ ha'st ((res_eq_one_iff ha'st).mpr hfix))

theorem Ctx.main (c : Ctx Γ L W₁ W₂ s) (F : A6Facts c.rL c.cL) {A : Subgroup (MulAut V)}
    (hA : IsA2 Γ A) (hq : commSeries A 2 = ⊥) (hle : rkIdx (fixV A) ≤ 2 * rk A) :
    rkIdx (fixV A) = 2 * rk A ∧ ∃ a ∈ A, rk A + 2 ≤ A6Rank a := by
  obtain ⟨hAΓ, hne, hel⟩ := hA
  have hsq : ∀ a ∈ A, a ^ 2 = 1 := hel.2
  have hlow : ∀ a ∈ A, A6Rank a ≤ rkIdx (fixV A) := by
    intro a ha
    unfold A6Rank
    exact rkIdx_anti fun v hv x hx => hv x ((Subgroup.zpowers_le.mpr ha) hx)
  obtain ⟨⟨a₀, ha₀A⟩, ha₀1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  have h3 : 3 ≤ rkIdx (fixV A) :=
    (c.three_le_rank F (hAΓ ha₀A) (hsq _ ha₀A) fun h => ha₀1 (Subtype.ext h)).trans (hlow _ ha₀A)
  have hm2 : 2 ≤ rk A := by omega
  have hcardA : Nat.card A = 2 ^ rk A := card_eq_two_pow_of_isPGroup hel.isPGroup
  have hcard4 : 4 ≤ Nat.card A := by
    rw [hcardA]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ rk A := Nat.pow_le_pow_right (by norm_num) hm2
  have hstab : A ≤ stabSub W₁ := c.A_le_stab F hAΓ hsq hq hcard4
  have hN : Nat.card A ≤ 2 * Nat.card ↥(A ⊓ L) :=
    card_le_two_mul_card_inf fun x hx hxL y hy hyL =>
      c.inv_mul_mem_L F (hAΓ hx) (hAΓ hy) (hstab hx) (hstab hy) hxL hyL
  have hNge : 2 ^ (rk A - 1) ≤ Nat.card ↥(A ⊓ L) := by
    have h1 : 2 ^ rk A = 2 * 2 ^ (rk A - 1) := by
      rw [← pow_succ']
      congr 1
      omega
    rw [hcardA, h1] at hN
    exact Nat.le_of_mul_le_mul_left hN (by norm_num)
  have hN2 : 2 ≤ Nat.card ↥(A ⊓ L) :=
    le_trans (by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (rk A - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)) hNge
  have hnt : Nontrivial ↥(A ⊓ L) := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨⟨a, haAL⟩, ha1⟩ := exists_ne (1 : ↥(A ⊓ L))
  have h4 : 4 ≤ A6Rank a := by
    have := c.rank_of_mem_L F haAL.2 (fun h => ha1 (Subtype.ext h)) (hsq a haAL.1)
    omega
  have h4' : 4 ≤ rkIdx (fixV A) := h4.trans (hlow a haAL.1)
  by_cases hm : rk A = 2
  · exact ⟨by omega, a, haAL.1, by omega⟩
  · exfalso
    have hN4 : 4 ≤ Nat.card ↥(A ⊓ L) :=
      le_trans (by
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ (rk A - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)) hNge
    obtain ⟨⟨a, haAL⟩, ⟨b, hbAL⟩, hab, ha1, hb1⟩ := exists_two_ne_one hN4
    have hab' : a ≠ b := fun h => hab (Subtype.ext h)
    have ha1' : a ≠ 1 := fun h => ha1 (Subtype.ext h)
    have hb1' : b ≠ 1 := fun h => hb1 (Subtype.ext h)
    have ha2 : (⟨a, haAL.2⟩ : ↥L) ^ 2 = 1 := Subtype.ext (by simpa using hsq a haAL.1)
    have hb2 : (⟨b, hbAL.2⟩ : ↥L) ^ 2 = 1 := Subtype.ext (by simpa using hsq b hbAL.1)
    have hq1 : A6QuadPair (c.rL ⟨a, haAL.2⟩) (c.rL ⟨b, hbAL.2⟩) := by
      intro w
      refine Subtype.ext ?_
      have := quad_apply hq haAL.1 hbAL.1 (w : V)
      show a (b w * (w : V)⁻¹) * (b w * (w : V)⁻¹)⁻¹ = 1
      rw [this]
      exact mul_inv_cancel _
    have hq2 : A6QuadPair (c.rL (c.cL.symm ⟨a, haAL.2⟩)) (c.rL (c.cL.symm ⟨b, hbAL.2⟩)) := by
      intro w
      refine Subtype.ext ?_
      show (s⁻¹ * a * s) ((s⁻¹ * b * s) w * (w : V)⁻¹) *
        ((s⁻¹ * b * s) w * (w : V)⁻¹)⁻¹ = 1
      have h1 := quad_apply hq haAL.1 hbAL.1 (s (w : V))
      have h2 : (s⁻¹ * b * s) (w : V) * (w : V)⁻¹ = s⁻¹ (b (s w) * (s w)⁻¹) := by
        simp [MulAut.mul_apply]
      have h3 : (s⁻¹ * a * s) (s⁻¹ (b (s w) * (s w)⁻¹)) = s⁻¹ (b (s w) * (s w)⁻¹) := by
        have : (s⁻¹ * a * s) (s⁻¹ (b (s w) * (s w)⁻¹)) = s⁻¹ (a (b (s w) * (s w)⁻¹)) := by
          simp [MulAut.mul_apply]
        rw [this, h1]
      rw [h2, h3]
      exact mul_inv_cancel _
    exact F.a6 ⟨a, haAL.2⟩ ⟨b, hbAL.2⟩ (fun h => hab' (congrArg Subtype.val h))
      (fun h => ha1' (congrArg Subtype.val h)) (fun h => hb1' (congrArg Subtype.val h)) ha2 hb2
      (Subtype.ext (hel.1 a haAL.1 b hbAL.1)) ⟨hq1, hq2⟩

end Quadratic

end CFSG.Quasithin.A6Amt

namespace CFSG.Quasithin

theorem a6Amt_of_fin (h : A6Fin) : A6Amt := by
  intro V _ _ hV Γ L W₁ W₂ s hLΓ hnorm hs hsup hW₁ hW₂ hW₂s hrk hirr hiso hfuse A hA hq hle
  have c : A6Amt.Ctx Γ L W₁ W₂ s :=
    ⟨hV, hLΓ, hnorm, hs, hsup, hW₁, hW₂, hW₂s, hrk, hirr, hiso, hfuse⟩
  exact c.main (c.facts h) hA hq hle

end CFSG.Quasithin
