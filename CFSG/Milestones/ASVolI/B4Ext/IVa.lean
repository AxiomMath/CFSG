module

public import CFSG.Milestones.ASVolI.B4Ext.GL5
public import CFSG.Milestones.ASVolI.B4Ext.WT

public section

namespace CFSG.ASVolI

open CFSG.Quasithin Module

section IVa

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

theorem burnsideB49x_wfix_eq {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (E : Subgroup (W ≃ₗ[ZMod 2] W)) : burnsideB49x_wfix E = burnsideB49x_gl_fix E :=
  Submodule.ext fun _ => Iff.rfl

theorem burnsideB49x_wcomm_eq {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (E : Subgroup (W ≃ₗ[ZMod 2] W)) : burnsideB49x_wcomm E = burnsideB49x_gl_comm E := rfl

variable {V : Type} [CommGroup V] [Finite V] (hV : ∀ v : V, v ^ 2 = 1) {K : Type} [Field K]
  [Finite K] {G : Subgroup (MulAut V)} {U : Subgroup V}
  {π : ↥(CFSG.Open.StatedSL 5 K) →* ↥G}

include hV in
theorem burnsideB49x_five_quad (hK : Nat.card K = 2)
    (hreal : (FFModel.nat (CFSG.Open.StatedSL 5 K)).RealizesVia G U ⊥ π)
    (hdual : CFSG.ASVolI.ChB.QuotIsoDual G U) {A : Subgroup (MulAut V)} (hAG : A ≤ G)
    (hA : IsElemAbelian2 A) (hne : A ≠ ⊥) (hoff : Nat.card V ≤ Nat.card A * Nat.card (fixV A)) :
    burnsideB49x_wcomm (burnsideB49x_hatW hV U G (burnsideB49_hG hreal) A) ≤
        burnsideB49x_wfix (burnsideB49x_hatW hV U G (burnsideB49_hG hreal) A) ∧
      ((5 - finrank (ZMod 2) (burnsideB49x_wfix
          (burnsideB49x_hatW hV U G (burnsideB49_hG hreal) A)) = 2 ∧
          finrank (ZMod 2) (burnsideB49x_wcomm
            (burnsideB49x_hatW hV U G (burnsideB49_hG hreal) A)) = 2) ∨
        (5 - finrank (ZMod 2) (burnsideB49x_wfix
          (burnsideB49x_hatW hV U G (burnsideB49_hG hreal) A)) = 2 ∧
          finrank (ZMod 2) (burnsideB49x_wcomm
            (burnsideB49x_hatW hV U G (burnsideB49_hG hreal) A)) = 3) ∨
        (5 - finrank (ZMod 2) (burnsideB49x_wfix
          (burnsideB49x_hatW hV U G (burnsideB49_hG hreal) A)) = 3 ∧
          finrank (ZMod 2) (burnsideB49x_wcomm
            (burnsideB49x_hatW hV U G (burnsideB49_hG hreal) A)) = 2)) ∧
      2 ^ ((5 - finrank (ZMod 2) (burnsideB49x_wfix
          (burnsideB49x_hatW hV U G (burnsideB49_hG hreal) A))) +
        finrank (ZMod 2) (burnsideB49x_wcomm
          (burnsideB49x_hatW hV U G (burnsideB49_hG hreal) A))) ≤ Nat.card A ∧
      Nat.card A ≤ 2 ^ ((5 - finrank (ZMod 2) (burnsideB49x_wfix
          (burnsideB49x_hatW hV U G (burnsideB49_hG hreal) A))) *
        finrank (ZMod 2) (burnsideB49x_wcomm
          (burnsideB49x_hatW hV U G (burnsideB49_hG hreal) A))) := by
  set hG := burnsideB49_hG hreal with hGdef
  set Â := burnsideB49x_hatW hV U G hG A with hÂ
  have hquot : CFSG.ASVolI.ChB.QuotIsoSub G U ∨ CFSG.ASVolI.ChB.QuotIsoDual G U := Or.inr hdual
  haveI : Finite (burnsideB49_W hV U) := inferInstance
  haveI : FiniteDimensional (ZMod 2) (burnsideB49_W hV U) := Module.Finite.of_finite
  have hn : finrank (ZMod 2) (burnsideB49_W hV U) = 5 := burnsideB49_finrank_W hV hK hreal hquot
  have hcard : Nat.card Â = Nat.card A :=
    burnsideB49x_card_hatW hV U G hG (burnsideB49_iota_injective hV hreal hquot) hAG
  have h1 := burnsideB49x_offender_dual hV hK hreal hdual hAG hoff
  have h2 := burnsideB49x_card_le_hom Â
  rw [hn] at h2
  set c := finrank (ZMod 2) (burnsideB49x_wfix Â) with hcdef
  set b := finrank (ZMod 2) (burnsideB49x_wcomm Â) with hbdef
  have hcn : c ≤ 5 := hn ▸ Submodule.finrank_le _
  have h3 : (5 - c) + b ≤ (5 - c) * b :=
    (Nat.pow_le_pow_iff_right (by norm_num)).1 (h1.trans h2)
  have h2A : 2 ≤ Nat.card A := by
    have : 1 < Nat.card A := by
      rw [Subgroup.one_lt_card_iff_ne_bot]
      exact hne
    omega
  have h4 : 1 ≤ (5 - c) * b := by
    by_contra h0
    have h0' : (5 - c) * b = 0 := by omega
    rw [h0', pow_zero, hcard] at h2
    omega
  have hx : 2 ≤ 5 - c := by
    by_contra h
    rcases Nat.lt_or_ge (5 - c) 1 with h' | h'
    · have : 5 - c = 0 := by omega
      rw [this, zero_mul] at h4
      omega
    · have : 5 - c = 1 := by omega
      rw [this] at h3
      omega
  have hy : 2 ≤ b := by
    by_contra h
    rcases Nat.lt_or_ge b 1 with h' | h'
    · have : b = 0 := by omega
      rw [this, mul_zero] at h4
      omega
    · have : b = 1 := by omega
      rw [this] at h3
      omega
  obtain ⟨hc, hs⟩ := burnsideB49x_hatW_elem hV U G hG hA
  have hquad : burnsideB49x_wcomm Â ≤ burnsideB49x_wfix Â := by
    rw [burnsideB49x_wfix_eq, burnsideB49x_wcomm_eq]
    by_cases hx2 : 5 - c ≤ 2
    · refine burnsideB49x_gl_quad_of_codim hc hs ?_
      rw [← burnsideB49x_wfix_eq, hn]
      omega
    by_cases hy2 : b ≤ 2
    · refine burnsideB49x_gl_quad_of_comm_le hc hs ?_
      rw [← burnsideB49x_wcomm_eq]
      exact hy2
    · refine burnsideB49x_gl5_quad hn hc hs ?_
      calc 64 = 2 ^ 6 := by norm_num
        _ ≤ 2 ^ ((5 - c) + b) := Nat.pow_le_pow_right (by norm_num) (by omega)
        _ ≤ Nat.card Â := h1
  have hbc : b ≤ c := Submodule.finrank_mono hquad
  refine ⟨hquad, ?_, hcard ▸ h1, hcard ▸ h2⟩
  omega

end IVa

end CFSG.ASVolI
