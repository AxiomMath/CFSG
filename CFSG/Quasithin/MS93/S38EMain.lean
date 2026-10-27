module

public import CFSG.Quasithin.MS93.S38EIII
public import CFSG.Quasithin.MS93.S38EDual
public import CFSG.Quasithin.MS93.S38EStmtA

public section

namespace CFSG.Quasithin.MS93.S38E

open CFSG.Quasithin CFSG.Quasithin.Fan86.Univ CFSG.Quasithin.MS93 CFSG.QuasithinUnique
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}

theorem card_lstar_cases (h : PUHyp M T L)
    (hcases : IsHatA6U M T L ∨ IsDoubleSL3U M T L ∨ IsSL3TwoU M T L ∨ IsSL3TwoZ M T L ∨
      IsSp4DerSec L (Uq M T L) (Uq M T L ⊓ Zq M L) 1) :
    Nat.card (S32.Lstar L) = 360 ∨
      ∃ m, 1 ≤ m ∧ Nat.card (S32.Lstar L) = CFSG.Open.ordA 2 (2 ^ m) := by
  rcases hcases with hX | hX | hX | hX | hX
  · exact Or.inl (card_lstar_of_isHatA6U h hX)
  · exact Or.inr (card_lstar_of_isDoubleSL3U h hX)
  · exact Or.inr ⟨1, le_rfl, card_lstar_of_isSL3TwoU h hX⟩
  · exact Or.inr ⟨1, le_rfl, card_lstar_of_isSL3TwoZ h hX⟩
  · exact Or.inl (card_lstar_of_isAltSix h hX)

theorem cases_of_card_lstar (h : PUHyp M T L)
    (hcases : IsHatA6U M T L ∨ IsDoubleSL3U M T L ∨ IsSL3TwoU M T L ∨ IsSL3TwoZ M T L ∨
      IsSp4DerSec L (Uq M T L) (Uq M T L ⊓ Zq M L) 1)
    (h360 : Nat.card (S32.Lstar L) = 360) :
    IsHatA6U M T L ∨ IsSp4DerSec L (Uq M T L) (Uq M T L ⊓ Zq M L) 1 := by
  rcases hcases with hX | hX | hX | hX | hX
  · exact Or.inl hX
  · obtain ⟨m, hm, hA⟩ := card_lstar_of_isDoubleSL3U h hX
    exact absurd (hA.symm.trans h360) (S32.ordA_two_ne_360 hm)
  · exact absurd ((card_lstar_of_isSL3TwoU h hX).symm.trans h360) (S32.ordA_two_ne_360 le_rfl)
  · exact absurd ((card_lstar_of_isSL3TwoZ h hX).symm.trans h360) (S32.ordA_two_ne_360 le_rfl)
  · exact Or.inr hX

theorem two_le_relIndex_xm (h : PUHyp M T L) {α' : Vtx (puAmalgam h.le)}
    (hc : IsCritical _ (baseA _) α') (hgeo : geo _ (baseA _) α' 1 = baseB _) :
    2 ≤ (Qv (puAmalgam h.le) (baseA _)).relIndex (XM _ α') := by
  have hb0 := h.critDist_pos
  have hne1 : (Qv (puAmalgam h.le) (baseA _)).relIndex (XM _ α') ≠ 1 := by
    rw [Ne, Subgroup.relIndex_eq_one]
    exact xm_not_le_qv_of_isCritical h.hyp20 hb0 h.centHyp hc
  have hXβ : XM (puAmalgam h.le) α' ≤ Qv _ (baseB _) := by
    rw [← hgeo]
    exact xm_le_qv_geo_one _ h.hyp20 hb0 h.centHyp hc
  have hfin : Finite ↥(XM (puAmalgam h.le) α') := by
    have : Finite ↥(imM h.le T) := finite_imM' h.le T
    rw [puAmalgam.qv_baseB] at hXβ
    exact Finite.of_injective _ (Subgroup.inclusion_injective hXβ)
  have hne0 : (Qv (puAmalgam h.le) (baseA _)).relIndex (XM _ α') ≠ 0 := by
    unfold Subgroup.relIndex
    exact Subgroup.index_ne_zero_of_finite
  omega

theorem s38End_of (h14 : MS14AS) (hSQ : SQTKQuot) (hT : S32.TypeFacts) (hB : SL3SecBound)
    (hD6 : D6Case) : S38End := by
  intro G _ _ M T L h hcent hXL hcases h1 h2 hD hCU hord hb hstar h8
  obtain ⟨α', hc, hgeo⟩ := exists_isCritical_geo _ h.hyp20 h.critDist_pos (PU.isMVtx_baseA _)
    (adj_baseA_baseB _)
  have hS := endSetup_base h hD hCU hb hstar h8 hc hgeo
  obtain ⟨lam, hlam1, hlamc⟩ := hS.exists_lam
  have htype := card_lstar_cases h hcases
  have he2 := two_le_relIndex_xm h hc hgeo
  rcases hord with hord | hdbl
  ·
    have he := e_eq_two_or_four h hD hord hc hgeo
    have hirr := hS.irrSec lam hlam1 he hlamc
    have hconc := h14 _ (hS.sq_SM lam hlam1) _ _ (hS.ffHyp_rhoM h lam hlam1 hirr he2 hSQ)
    refine hS.false_of_ffConclusion h lam hlam1 hirr he2 hT hconc htype fun h360 halt => ?_
    exact hD6 G M T L h hcent hXL (cases_of_card_lstar h hcases h360) h1 h2 hD hCU hord hb hstar
      h8 α' hc hgeo lam hlam1 hlamc halt
  ·
    obtain ⟨F, -, hF, hFX, heF⟩ := exists_isXOff_imM_eq h hD hc hgeo
    have : Finite (hS.YM lam) := hS.finite_YM lam
    have hirr := irrSec_commV_of_big (yPairing hS.cls2 lam) (hS.pairing_isInv lam hlam1)
      (hS.kY_le lam hlam1) (hS.eY_le lam hlam1) (hS.range_le_normalizer_kY lam hlam1)
      (hS.kY_perfect lam hlam1) (hS.index_fixV_eY_le lam hlam1)
      (fun W N hirr hnc => hS.lt_aI_mul_cI h lam hlam1 W N hirr hnc h14 hSQ hT hB hcent hdbl hF
        hFX heF he2) (hS.nonCent_top lam hlam1 hlamc)
    have hconc := h14 _ (hS.sq_SM lam hlam1) _ _ (hS.ffHyp_rhoM h lam hlam1 hirr he2 hSQ)
    refine hS.false_of_ffConclusion h lam hlam1 hirr he2 hT hconc htype fun h360 _ => ?_
    obtain ⟨m, hm, hA⟩ := card_lstar_of_isDoubleSL3U h hdbl
    exact S32.ordA_two_ne_360 hm (hA.symm.trans h360)

end CFSG.Quasithin.MS93.S38E
