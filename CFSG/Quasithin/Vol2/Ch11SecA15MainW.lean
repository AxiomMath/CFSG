module

public import CFSG.Quasithin.Vol2.Ch11SecA15S5b
public import CFSG.Quasithin.MS93.C134CorrM
public import CFSG.Quasithin.Vol2.Ch11SecA15Excl2W

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecA

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G} {n : ℕ} {V₁ : Subgroup G}

theorem block_of_not_leW (h331 : Stmt3_3_1) (h132 : ASInputs.AS_C_1_32)
    (h134 : MS93.AS_C_1_34_corrM) (hF : Facts15) (hF11 : Facts11) (hN : NatFacts)
    (hG2 : FactG2DerivedOrder) (h1102 : Stmt11_0_2) (h1103 : Stmt11_0_3) (h1110 : Stmt11_1_0)
    (h : Hyp11 G T L I n) (hU : IsVi T L I n 1 V₁)
    (hNot : ¬ Subgroup.normalizer (ROf T L V₁ : Set G) ≤ Subgroup.normalizer (L : Set G)) :
    IsSL3Block L ∨ IsSp4Block L := by
  have hMS := isMSPair h331 hF hN h1102 h hU hNot
  have hLc := L_mem_cComp_msG0 (V₁ := V₁) h
  have hG0 := coe_msG0 (V₁ := V₁) h
  rcases h132 G _ _ L hMS hLc hG0 with hB | hB | hB | hB | ⟨m, F, hF', hFt, α, hcard, hα⟩
  · exact (not_isG2Block hG2 h1102 h hB).elim
  · exact (not_isAltBlockType_six hG2 h1102 h hB).elim
  · exact Or.inr hB
  · exact (not_isHatA6Block hG2 h1102 h hB).elim
  · obtain ⟨i, hi⟩ := h134 G _ _ L hMS hLc hG0 ⟨m, F, hF', hFt, α, hcard, hα⟩
    match i, hi with
    | 1, hi => exact Or.inl hi.1
    | 2, hi => exact (not_isC134Case2 hF hF11 hG2 h1102 h1103 h1110 h hU hi).elim
    | 3, hi => exact (not_isC134Case3 hF hF11 hG2 h1102 h1103 h1110 h hU hi).elim
    | 4, hi => exact (not_isC134Case4W hF hF11 hG2 h1102 h1103 h1110 h hU hi).elim
    | 5, hi => exact (not_modO2Surj_SL3_two hG2 h1102 h hi.1.choose_spec.1).elim
    | 0, hi => exact hi.elim
    | (k + 6), hi => exact hi.elim

theorem stmt11_1_5_ofW (h331 : Stmt3_3_1) (h132 : ASInputs.AS_C_1_32)
    (h134 : MS93.AS_C_1_34_corrM) (h4213 : TmpL6_4_2_13) (hF : Facts15) (hFc : Facts15c)
    (hF11 : Facts11) (hN : NatFacts) (hG2 : FactG2DerivedOrder) (h1102 : Stmt11_0_2)
    (h1103 : Stmt11_0_3) (h1104 : Stmt11_0_4) (h1110 : Stmt11_1_0) : Stmt11_1_5 := by
  intro G _ _ T L I n V₁ h hU
  by_cases hNot : Subgroup.normalizer (ROf T L V₁ : Set G) ≤ Subgroup.normalizer (L : Set G)
  · exact Or.inl hNot
  · right
    have hB := block_of_not_leW h331 h132 h134 hF hF11 hN hG2 h1102 h1103 h1110 h hU hNot
    have hC := inf_centralizer_eq_bot h331 h4213 h1104 hF hFc hF11 hG2 h1102 h1103 h hU hB hNot
    exact ⟨fsuV_eq_VM h1102 h (IsSL3Block_or_IsSp4Block.isShort2 hB), hB, hC,
      V1_eq_omegaOneCenterOf hF hFc hG2 h1102 h hU hB hC⟩

end CFSG.Quasithin.Vol2.Ch11.SecA
