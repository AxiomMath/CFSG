module

public import CFSG.Quasithin.EmptyFaithful.S153EQuad
public import CFSG.Quasithin.EmptyFaithful.S153E51B

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.S1417 CFSG.LieType.BorelTits
open scoped commutatorElement Pointwise

namespace S153E

section Bar53

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ : Subgroup G} {t : G}

noncomputable abbrev qW (cx : Ctx15350 T Mc M V₁ V₂ t) :
    IntMod (VZ T M) cx.c.hyp.elemAbelian → ZMod 2 := qV153 cx.c

theorem qW_spec (cx : Ctx15350 T Mc M V₁ V₂ t) :
    IsQuadraticFormOn (qW cx) ∧ IsNondegQuadratic (qW cx) ∧ IsPlusType (qW cx) ∧
      autI cx.c.hyp.elemAbelian M = orthogonalGroupOf (qW cx) :=
  let h := qV153_spec cx.c
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩

theorem card_fixV_autI_T (cx : Ctx15350 T Mc M V₁ V₂ t) :
    Nat.card ↥(fixV (autI cx.c.hyp.elemAbelian T)) = 2 := by
  rw [card_fixV_autI cx.c.hyp.elemAbelian (T_le_N cx), ← cx.c.hyp.lemma_15_3_2_two.1]
  exact cx.c.hyp.lemma_15_3_2_two.2

theorem mem_fixV_autI_T_iff (cx : Ctx15350 T Mc M V₁ V₂ t)
    (w : IntMod (VZ T M) cx.c.hyp.elemAbelian) :
    w ∈ fixV (autI cx.c.hyp.elemAbelian T) ↔ w.val ∈ quasithinOmegaOneCenter T := by
  rw [mem_fixV_autI cx.c.hyp.elemAbelian (T_le_N cx), cx.c.hyp.lemma_15_3_2_two.1]
  constructor
  · intro h
    exact ⟨w.val_mem, h⟩
  · intro h
    exact h.2

theorem commV_autI_U_eq_perp (cx : Ctx15350 T Mc M V₁ V₂ t) (h1 : ¬ VZ T M ≤ pCoreOf 2 Mc)
    (hUS : ¬ UH153 T M V₁ Mc ≤ Sgp153 T V₁) :
    commV (autI cx.c.hyp.elemAbelian (UH153 T M V₁ Mc)) =
        perpSub (qW_spec cx).1 (fixV (autI cx.c.hyp.elemAbelian T)) ∧
      Nat.card ↥(commV (autI cx.c.hyp.elemAbelian (UH153 T M V₁ Mc))) = 8 := by
  obtain ⟨L₁, L₂, tb, s₁, s₂, τ, a₁, a₂, hS, hF, hV₁, -⟩ := exists_bar_model cx
  have hT := cx.c.hyp.isSylowTwoOf_autI
  have hexp' : ∀ w : IntMod (VZ T M) cx.c.hyp.elemAbelian, w ^ 2 = 1 := fun w => IntMod.sq_eq_one w
  have hexp : ∀ w : IntMod (VZ T M) cx.c.hyp.elemAbelian, w * w = 1 := fun w => by
    rw [← pow_two]
    exact hexp' w
  have hcard16 : Nat.card (IntMod (VZ T M) cx.c.hyp.elemAbelian) = 16 := cx.c.hyp.card_VZ
  have hr : s₁ * s₂ ∈ autI cx.c.hyp.elemAbelian (UH153 T M V₁ Mc) := mul_mem_autI_U cx h1 hS hF
  have hNS := not_autI_U_le_sup cx hS hV₁ hUS
  obtain ⟨x, hxU, hxN⟩ := IsConcreteLE.not_le_iff_exists.mp hNS
  have hxT : x ∈ autI cx.c.hyp.elemAbelian T := autI_U_le_T cx hxU
  have hxx : x * x = 1 := autI_U_sq cx hxU
  have hrr : (s₁ * s₂) * (s₁ * s₂) = 1 := autI_U_sq cx hr
  have hA : autI cx.c.hyp.elemAbelian (UH153 T M V₁ Mc) ≤ orthogonalGroupOf (qW cx) := by
    intro g hg
    have : g ∈ autI cx.c.hyp.elemAbelian M :=
      autI_mono cx.c.hyp.elemAbelian ((U_le_T cx).trans (T_le_M cx)) hg
    rw [(qW_spec cx).2.2.2] at this
    exact this
  have hfr : Nat.card ↥(fixV (Subgroup.zpowers (s₁ * s₂))) = 4 :=
    card_fixV_mul_s hexp' hS hF.sylow
  have hfx : Nat.card ↥(fixV (Subgroup.zpowers x)) = 4 := by
    have := T1531O4.rk_fixV_swap_one hS hexp' (hT.1 hxT) hxN hxx
    rw [card_eq_two_pow hexp', this]
    norm_num
  have hZb : Nat.card ↥(fixV (autI cx.c.hyp.elemAbelian T)) = 2 := card_fixV_autI_T cx
  have hne : fixV (Subgroup.zpowers (s₁ * s₂)) ≠ fixV (Subgroup.zpowers x) := by
    intro heq
    have hrS : s₁ * s₂ ∈ autI cx.c.hyp.elemAbelian T ⊓ (L₁ ⊔ L₂) :=
      (hF.S_eq _).2 (Or.inr (Or.inr (Or.inr rfl)))
    have hfixS : fixV (autI cx.c.hyp.elemAbelian T ⊓ (L₁ ⊔ L₂)) =
        fixV (Subgroup.zpowers (s₁ * s₂)) :=
      Subgroup.eq_of_le_of_card_ge (fixV_anti (Subgroup.zpowers_le.mpr hrS))
        (by rw [hfr, hF.card_fix])
    have hAle : fixV (Subgroup.zpowers (s₁ * s₂)) ≤ fixV (autI cx.c.hyp.elemAbelian T) := by
      intro a ha y hy
      have haS : a ∈ fixV (autI cx.c.hyp.elemAbelian T ⊓ (L₁ ⊔ L₂)) := by
        rw [hfixS]
        exact ha
      have hax : a ∈ fixV (Subgroup.zpowers x) := by
        rw [← heq]
        exact ha
      have hxS : x ∉ autI cx.c.hyp.elemAbelian T ⊓ (L₁ ⊔ L₂) := fun h => hxN h.2
      have h2 : x a = a := mem_fixV_zpowers_iff.mp hax
      rcases coset_of_relIndex_two (hS.relIndex_S hT) hy hxT hxS with h | h
      · exact haS y h
      · have h3 : (y * x⁻¹) a = a := haS _ h
        calc y a = (y * x⁻¹) (x a) := by simp [MulAut.mul_apply]
          _ = (y * x⁻¹) a := by rw [h2]
          _ = a := h3
    have := Subgroup.card_le_of_le hAle
    rw [hfr, hZb] at this
    omega
  have hfU : Nat.card ↥(fixV (autI cx.c.hyp.elemAbelian (UH153 T M V₁ Mc))) = 2 := by
    have hge : 2 ≤ Nat.card ↥(fixV (autI cx.c.hyp.elemAbelian (UH153 T M V₁ Mc))) := by
      rw [← hZb]
      exact Subgroup.card_le_of_le (fixV_anti (autI_U_le_T cx))
    have hsub : fixV (autI cx.c.hyp.elemAbelian (UH153 T M V₁ Mc)) ≤
        fixV (Subgroup.zpowers (s₁ * s₂)) ⊓ fixV (Subgroup.zpowers x) :=
      le_inf (fixV_anti (Subgroup.zpowers_le.mpr hr)) (fixV_anti (Subgroup.zpowers_le.mpr hxU))
    have hle1 := Subgroup.card_le_of_le hsub
    have hdvd : Nat.card ↥(fixV (Subgroup.zpowers (s₁ * s₂)) ⊓ fixV (Subgroup.zpowers x)) ∣ 4 := by
      rw [← hfr]
      exact Subgroup.card_dvd_of_le inf_le_left
    have hn4 : Nat.card ↥(fixV (Subgroup.zpowers (s₁ * s₂)) ⊓ fixV (Subgroup.zpowers x)) ≠ 4 := by
      intro h4
      apply hne
      have hle : fixV (Subgroup.zpowers (s₁ * s₂)) ⊓ fixV (Subgroup.zpowers x) ≤
          fixV (Subgroup.zpowers (s₁ * s₂)) := inf_le_left
      have e1 := Subgroup.eq_of_le_of_card_ge hle (by rw [h4, hfr])
      have hle2 : fixV (Subgroup.zpowers (s₁ * s₂)) ≤ fixV (Subgroup.zpowers x) := by
        rw [← e1]
        exact inf_le_right
      exact Subgroup.eq_of_le_of_card_ge hle2 (by rw [hfr, hfx])
    have hb2 : Nat.card ↥(fixV (Subgroup.zpowers (s₁ * s₂)) ⊓ fixV (Subgroup.zpowers x)) ≤ 2 := by
      have hb4 := Nat.le_of_dvd (by norm_num) hdvd
      generalize Nat.card ↥(fixV (Subgroup.zpowers (s₁ * s₂)) ⊓ fixV (Subgroup.zpowers x)) = b
        at hdvd hn4 hb4 ⊢
      interval_cases b <;> omega
    omega
  have hfT : fixV (autI cx.c.hyp.elemAbelian T) =
      fixV (autI cx.c.hyp.elemAbelian (UH153 T M V₁ Mc)) :=
    Subgroup.eq_of_le_of_card_ge (fixV_anti (autI_U_le_T cx)) (by rw [hfU, hZb])
  obtain ⟨hc, hc8⟩ := commV_eq_perpSub (qW_spec cx).1 (qW_spec cx).2.1 hexp hcard16 hA hr hxU hrr
    hxx hfr hfx hne hfU
  rw [← hfT] at hc
  exact ⟨hc, hc8⟩

end Bar53

end S153E

end CFSG.Quasithin
