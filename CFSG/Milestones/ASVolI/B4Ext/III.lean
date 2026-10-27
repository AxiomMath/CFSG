module

public import CFSG.Milestones.ASVolI.B4Ext.WT
public import CFSG.Milestones.ASVolI.B4Ext.Flag
public import CFSG.Milestones.ASVolI.B4Ext.GL4
public import CFSG.Quasithin.Background.B3Q

public section

namespace CFSG.ASVolI

open CFSG.Quasithin Module

section III

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

variable {V : Type} [CommGroup V] [Finite V] (hV : ∀ v : V, v ^ 2 = 1) {K : Type} [Field K]
  [Finite K] {G : Subgroup (MulAut V)} {U : Subgroup V}
  {π : ↥(CFSG.Open.StatedSL 4 K) →* ↥G}

include hV in
theorem burnsideB49x_four_card_le (hK : Nat.card K = 2)
    (hreal : (FFModel.nat (CFSG.Open.StatedSL 4 K)).RealizesVia G U ⊥ π)
    (hquot : CFSG.ASVolI.ChB.QuotIsoSub G U ∨ CFSG.ASVolI.ChB.QuotIsoDual G U)
    {A : Subgroup (MulAut V)} (hAG : A ≤ G) (hA : IsElemAbelian2 A) :
    Nat.card A ≤ 16 ∧ (16 ≤ Nat.card A → ∃ X : Submodule (ZMod 2) (burnsideB49_W hV U),
      finrank (ZMod 2) X = 2 ∧
        burnsideB49x_hatW hV U G (burnsideB49_hG hreal) A = burnsideB49x_gl_Q X) := by
  set hG := burnsideB49_hG hreal with hGdef
  haveI : Finite (burnsideB49_W hV U) := inferInstance
  haveI : FiniteDimensional (ZMod 2) (burnsideB49_W hV U) := Module.Finite.of_finite
  have hn : finrank (ZMod 2) (burnsideB49_W hV U) = 4 := burnsideB49_finrank_W hV hK hreal hquot
  have hcard := burnsideB49x_card_hatW hV U G hG (burnsideB49_iota_injective hV hreal hquot) hAG
  obtain ⟨hc, hs⟩ := burnsideB49x_hatW_elem hV U G hG hA
  have key : 16 ≤ Nat.card A → ∃ X : Submodule (ZMod 2) (burnsideB49_W hV U),
      finrank (ZMod 2) X = 2 ∧ burnsideB49x_hatW hV U G hG A = burnsideB49x_gl_Q X := by
    intro h16
    rw [← hcard] at h16
    exact burnsideB49x_gl_four hn hc hs h16
  refine ⟨?_, key⟩
  by_contra hlt
  obtain ⟨X, hX, hAX⟩ := key (by omega)
  have h1 := burnsideB49x_gl_card_Q hX hn
  rw [← hAX, hcard] at h1
  norm_num at h1
  omega

include hV in
theorem burnsideB49x_four_sixteen (hK : Nat.card K = 2)
    (hreal : (FFModel.nat (CFSG.Open.StatedSL 4 K)).RealizesVia G U ⊥ π)
    (hdual : CFSG.ASVolI.ChB.QuotIsoDual G U) {A : Subgroup (MulAut V)} (hAG : A ≤ G)
    (hne : A ≠ ⊥) (hoff : Nat.card V ≤ Nat.card A * Nat.card (fixV A)) :
    4 ≤ (4 - finrank (ZMod 2) (burnsideB49x_wfix
        (burnsideB49x_hatW hV U G (burnsideB49_hG hreal) A))) +
      finrank (ZMod 2) (burnsideB49x_wcomm (burnsideB49x_hatW hV U G (burnsideB49_hG hreal) A)) ∧
    16 ≤ Nat.card A := by
  set hG := burnsideB49_hG hreal with hGdef
  have hquot : CFSG.ASVolI.ChB.QuotIsoSub G U ∨ CFSG.ASVolI.ChB.QuotIsoDual G U := Or.inr hdual
  haveI : Finite (burnsideB49_W hV U) := inferInstance
  haveI : FiniteDimensional (ZMod 2) (burnsideB49_W hV U) := Module.Finite.of_finite
  have hn : finrank (ZMod 2) (burnsideB49_W hV U) = 4 := burnsideB49_finrank_W hV hK hreal hquot
  have hcard := burnsideB49x_card_hatW hV U G hG (burnsideB49_iota_injective hV hreal hquot) hAG
  have h1 := burnsideB49x_offender_dual hV hK hreal hdual hAG hoff
  have h2 := burnsideB49x_card_le_hom (burnsideB49x_hatW hV U G hG A)
  rw [hn] at h2
  set c := finrank (ZMod 2) (burnsideB49x_wfix (burnsideB49x_hatW hV U G hG A)) with hcdef
  set b := finrank (ZMod 2) (burnsideB49x_wcomm (burnsideB49x_hatW hV U G hG A)) with hbdef
  have h3 : (4 - c) + b ≤ (4 - c) * b :=
    (Nat.pow_le_pow_iff_right (by norm_num)).1 (h1.trans h2)
  have h2A : 2 ≤ Nat.card A := by
    have : 1 < Nat.card A := by
      rw [Subgroup.one_lt_card_iff_ne_bot]
      exact hne
    omega
  have h4 : 1 ≤ (4 - c) * b := by
    by_contra h0
    have h0' : (4 - c) * b = 0 := by omega
    rw [h0', pow_zero, hcard] at h2
    omega
  have hx : 1 ≤ 4 - c := by
    rcases Nat.eq_zero_or_pos (4 - c) with h | h
    · rw [h, zero_mul] at h4
      omega
    · exact h
  have hy : 1 ≤ b := by
    rcases Nat.eq_zero_or_pos b with h | h
    · rw [h, mul_zero] at h4
      omega
    · exact h
  have hx2 : 2 ≤ 4 - c := by
    by_contra h
    have h' : 4 - c = 1 := by omega
    rw [h'] at h3
    omega
  have hy2 : 2 ≤ b := by
    by_contra h
    have h' : b = 1 := by omega
    rw [h'] at h3
    omega
  refine ⟨by omega, ?_⟩
  rw [← hcard]
  calc 16 = 2 ^ 4 := by norm_num
    _ ≤ 2 ^ ((4 - c) + b) := Nat.pow_le_pow_right (by norm_num) (by omega)
    _ ≤ _ := h1

include hV in
theorem burnsideB49x_four_Jj (hK : Nat.card K = 2)
    (hreal : (FFModel.nat (CFSG.Open.StatedSL 4 K)).RealizesVia G U ⊥ π)
    (hquot : CFSG.ASVolI.ChB.QuotIsoSub G U ∨ CFSG.ASVolI.ChB.QuotIsoDual G U)
    {T : Subgroup (MulAut V)} (hT : CFSG.QuasithinUnique.IsSylowTwoOf T G)
    {A : Subgroup (MulAut V)} (hAT : A ≤ T) (hA : IsElemAbelian2 A) (h16 : Nat.card A = 16) :
    CFSG.ASVolI.ChB.Jj T 0 = A := by
  set hG := burnsideB49_hG hreal with hGdef
  have hTG : T ≤ G := hT.1
  have hinj := burnsideB49_iota_injective hV hreal hquot
  haveI : Finite (burnsideB49_W hV U) := inferInstance
  haveI : FiniteDimensional (ZMod 2) (burnsideB49_W hV U) := Module.Finite.of_finite
  have hn : finrank (ZMod 2) (burnsideB49_W hV U) = 4 := burnsideB49_finrank_W hV hK hreal hquot
  have hTp : IsPGroup 2 (burnsideB49x_hatW hV U G hG T) := by
    have h1 : IsPGroup 2 (T.subgroupOf G) := hT.2.1.comap_subtype
    exact h1.map _
  obtain ⟨Y, hY, hYinv⟩ := burnsideB49x_exists_inv_two _ hTp (by omega)
  have hQY : ∀ E : Subgroup (MulAut V), E ≤ T → IsElemAbelian2 E → Nat.card E = 16 →
      burnsideB49x_hatW hV U G hG E = burnsideB49x_gl_Q Y := by
    intro E hET hE hE16
    obtain ⟨X, hX, hEX⟩ := (burnsideB49x_four_card_le hV hK hreal hquot (hET.trans hTG) hE).2
      hE16.ge
    have hXY : X = Y := burnsideB49x_gl_Q_stab hX hY (fun q hq y hy => by
      rw [← hEX] at hq
      have hle : burnsideB49x_hatW hV U G hG E ≤ burnsideB49x_hatW hV U G hG T :=
        Subgroup.map_mono (Subgroup.comap_mono hET)
      exact hYinv q (hle hq) y hy)
    rw [hEX, hXY]
  have huniq : ∀ E : Subgroup (MulAut V), E ≤ T → IsElemAbelian2 E → Nat.card E = 16 → E = A := by
    intro E hET hE hE16
    have h1 := (hQY E hET hE hE16).trans (hQY A hAT hA h16).symm
    have h2 : E.subgroupOf G = A.subgroupOf G := Subgroup.map_injective hinj h1
    have h3 := congrArg (fun S : Subgroup ↥G => S.map G.subtype) h2
    simp only [Subgroup.subgroupOf_map_subtype] at h3
    rwa [inf_eq_left.2 (hET.trans hTG), inf_eq_left.2 (hAT.trans hTG)] at h3
  have hrank : CFSG.pRank 2 ↥T = 4 := by
    have hbound : ∀ r ∈ {r : ℕ | ∃ B : Subgroup ↥T, CFSG.IsElementaryAbelian 2 B ∧
        Nat.card B = 2 ^ r}, r ≤ 4 := by
      rintro r ⟨B, hB, hBr⟩
      have hB' := burnsideB49x_isElemAbelian2_map B
      have hle := (burnsideB49x_four_card_le hV hK hreal hquot
        ((Subgroup.map_subtype_le B).trans hTG) hB').1
      rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective _), hBr] at hle
      exact (Nat.pow_le_pow_iff_right (show 1 < 2 by norm_num)).1
        (hle.trans (by norm_num : (16 : ℕ) ≤ 2 ^ 4))
    have hmem : 4 ∈ {r : ℕ | ∃ B : Subgroup ↥T, CFSG.IsElementaryAbelian 2 B ∧
        Nat.card B = 2 ^ r} := by
      refine ⟨A.subgroupOf T, burnsideB49x_isElementaryAbelian_subgroupOf hA, ?_⟩
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAT).toEquiv, h16]
      norm_num
    exact le_antisymm (csSup_le ⟨4, hmem⟩ hbound) (le_csSup ⟨4, hbound⟩ hmem)
  have hfam : CFSG.higherElemThompsonFamily ↥T 0 = {A.subgroupOf T} := by
    ext B
    rw [CFSG.mem_higherElemThompsonFamily_iff, hrank, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hB, hBc⟩
      have hB' := burnsideB49x_isElemAbelian2_map B
      have hE := huniq (B.map T.subtype) (Subgroup.map_subtype_le B) hB' (by
        rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective _), hBc]
        norm_num)
      rw [← hE]
      exact (Subgroup.comap_map_eq_self_of_injective (Subgroup.subtype_injective _) B).symm
    · rintro rfl
      refine ⟨burnsideB49x_isElementaryAbelian_subgroupOf hA, ?_⟩
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAT).toEquiv, h16]
      norm_num
  rw [CFSG.ASVolI.ChB.Jj_eq_higherElemThompson_of_le T 0 (Nat.zero_le _),
    CFSG.higherElemThompson, hfam, sSup_singleton, Subgroup.subgroupOf_map_subtype,
    inf_eq_left.2 hAT]

include hV in
theorem burnsideB49x_four_q (hK : Nat.card K = 2)
    (hreal : (FFModel.nat (CFSG.Open.StatedSL 4 K)).RealizesVia G U ⊥ π)
    (hdual : CFSG.ASVolI.ChB.QuotIsoDual G U) {A : Subgroup (MulAut V)}
    (hA : IsFFStarOffender G A) : qOf G = ((1 : ℚ) : WithTop ℚ) := by
  have hquot : CFSG.ASVolI.ChB.QuotIsoSub G U ∨ CFSG.ASVolI.ChB.QuotIsoDual G U := Or.inr hdual
  refine qOf_eq_of_offenders hV le_rfl (fun B hB => ?_) ⟨A, hA, B1_4_1 hV hA⟩
  set hG := burnsideB49_hG hreal with hGdef
  obtain ⟨h4, -⟩ := burnsideB49x_four_sixteen hV hK hreal hdual hB.1 hB.2.1
    (burnsideB49x_offender_card hB)
  have hle16 := (burnsideB49x_four_card_le hV hK hreal hquot hB.1 hB.2.2.1).1
  have hfix := burnsideB49x_card_fixV_le_dual hV hK hreal hdual B
  have hcardV := burnsideB49x_card_V_W hV hK hreal hquot
  haveI : Finite (burnsideB49_W hV U) := inferInstance
  haveI : FiniteDimensional (ZMod 2) (burnsideB49_W hV U) := Module.Finite.of_finite
  have hn : finrank (ZMod 2) (burnsideB49_W hV U) = 4 := burnsideB49_finrank_W hV hK hreal hquot
  set c := finrank (ZMod 2) (burnsideB49x_wfix (burnsideB49x_hatW hV U G hG B)) with hcdef
  set b := finrank (ZMod 2) (burnsideB49x_wcomm (burnsideB49x_hatW hV U G hG B)) with hbdef
  have hcn : c ≤ 4 := hn ▸ Submodule.finrank_le _
  have hbn : b ≤ 4 := hn ▸ Submodule.finrank_le _
  have hfix' : Nat.card ↥(fixV B) ≤ 2 ^ 4 := by
    refine hfix.trans ?_
    rw [← pow_add]
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have hBV : Nat.card B * Nat.card ↥(fixV B) ≤ Nat.card V := by
    rw [hcardV]
    calc Nat.card B * Nat.card ↥(fixV B) ≤ 16 * 2 ^ 4 := Nat.mul_le_mul hle16 hfix'
      _ = 2 ^ (2 * 4) := by norm_num
  by_contra hlt
  have hlt' := (rAV_lt_one_iff hV hB.isA2).1 (not_le.1 hlt)
  omega

end III

end CFSG.ASVolI
