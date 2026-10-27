module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.BBarDelta
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.GF2RepsNoO2Nine
public import CFSG.Quasithin.Background.RonanE43M22Three
public import CFSG.Quasithin.H13.A6S13821zz11
public import CFSG.Quasithin.EmptyFaithful.T1515C4Mod

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Open CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open scoped commutatorElement Pointwise

theorem bParam_le_three_of_M22
    {W : Type} [CommGroup W] [Finite W] (hw : ∀ w : W, w ^ 2 = 1)
    {Y L : Subgroup (MulAut W)} (hLY : L ≤ Y) (hN : (L.subgroupOf Y).Normal)
    (hSpor : IsSpor ↥L .M22) (hfix : fixV L = ⊥) :
    bParam L Y ≤ 3 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨eL0⟩ := hSpor
  have hSimpleL : IsSimpleGroup ↥L :=
    (MulEquiv.isSimpleGroup_congr eL0).mpr
      CFSG.Sporadic.Mathieu.fam_m22_simplicity.2.2
  have hcardL : Nat.card ↥L = 443520 := by
    rw [← CFSG.Sporadic.Mathieu.card_M22]
    exact Nat.card_congr eL0.toEquiv
  have hnonprime : ¬ (Nat.card ↥L).Prime := by
    rw [hcardL]
    norm_num
  have hnab : ∃ a b : ↥L, a * b ≠ b * a := by
    by_contra hc
    push Not at hc
    letI : CommGroup ↥L := { (inferInstance : Group ↥L) with mul_comm := hc }
    exact hnonprime (IsSimpleGroup.prime_card (α := ↥L))
  obtain ⟨hLq, hZL⟩ := CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hnab
  have hLqopen : CFSG.Open.IsQuasisimple ↥L :=
    CFSG.Quasithin.A3.isQuasisimple_iff_open.mp hLq
  have hLperf : ⁅L, L⁆ = L := by
    rw [← Subgroup.map_subtype_commutator L, hLq.1.commutator_eq_top, Subgroup.map_top,
      Subgroup.range_subtype]
  have hWnt : Nontrivial W := by
    by_contra hnt
    have hsub : Subsingleton W := not_nontrivial_iff_subsingleton.mp hnt
    have : Subsingleton (MulAut W) :=
      ⟨fun a b => MulEquiv.ext fun w => hsub.elim (a w) (b w)⟩
    have hLbot : L = ⊥ := Subgroup.eq_bot_of_subsingleton L
    rw [hLbot, Subgroup.card_bot] at hcardL
    norm_num at hcardL
  have : Nontrivial W := hWnt
  obtain ⟨T, hTsyl⟩ := CFSG.Quasithin.E1.exists_isSylowIn_two Y
  have hTY : T ≤ Y := hTsyl.le
  have hNLY : Y ≤ Subgroup.normalizer (L : Set (MulAut W)) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLY).mp hN
  have hstep0 : bParam L Y ≤ bParam L (L ⊔ T) :=
    bParam_le_of_normal hLY hNLY hTsyl
  have hLG₁ : L ≤ L ⊔ T := le_sup_left
  have hTG₁ : T ≤ L ⊔ T := le_sup_right
  have hG₁leY : L ⊔ T ≤ Y := sup_le hLY hTY
  have hG₁N : L ⊔ T ≤ Subgroup.normalizer (L : Set (MulAut W)) :=
    hG₁leY.trans hNLY
  have hNG₁ : (L.subgroupOf (L ⊔ T)).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer hG₁N
  have hcompG₁ : IsComponentOf L (L ⊔ T) :=
    ⟨hLG₁, IsSubnormal.step hLG₁ hNG₁ (IsSubnormal.refl (L ⊔ T)), hLqopen⟩
  have hmul := Subgroup.relIndex_mul_relIndex T (L ⊔ T) Y hTG₁ hG₁leY
  have hTsylG₁ : IsSylowIn 2 T (L ⊔ T) := by
    refine ⟨hTG₁, hTsyl.isPGroup, fun hdvd => hTsyl.not_dvd_relIndex ?_⟩
    rw [← hmul]
    exact dvd_mul_of_dvd_left hdvd _
  have hfixG₁ : fixV (L ⊔ T) = ⊥ := by
    refine le_bot_iff.mp ?_
    calc fixV (L ⊔ T) ≤ fixV L := fixV_anti hLG₁
      _ = ⊥ := hfix
  have hfixTne : fixV T ≠ ⊥ :=
    CFSG.Quasithin.H13.A6.A6S20.fixV_ne_bot_of_two_group hw hTsyl.isPGroup
  have hfixT : fixV T ≠ fixV (L ⊔ T) := by
    rw [hfixG₁]
    exact hfixTne
  let U : Subgroup W := fixV (pCoreOf 2 (L ⊔ T))
  have hst : L ⊔ T ≤ stabSub U := CFSG.Quasithin.B1Red.le_stabSub_fixV_pCoreOf (L ⊔ T)
  have hstL : L ≤ stabSub U := hLG₁.trans hst
  have hstT : T ≤ stabSub U := hTG₁.trans hst
  have hker : (L ⊔ T) ⊓ centSub U = pCoreOf 2 (L ⊔ T) :=
    inf_centSub_fixV_pCoreOf_eq hw hLG₁ hTG₁ rfl hcompG₁ hTsylG₁
  have hQleT : pCoreOf 2 (L ⊔ T) ≤ T :=
    hTsylG₁.le_of_normal (CFSG.LieType.BorelTits.pCoreOf_le 2 (L ⊔ T))
      ((Subgroup.normal_subgroupOf_iff_le_normalizer
        (CFSG.LieType.BorelTits.pCoreOf_le 2 (L ⊔ T))).mpr
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (L ⊔ T)))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (L ⊔ T))
  have hLQcomm : ⁅L, pCoreOf 2 (L ⊔ T)⁆ = ⊥ :=
    CFSG.Quasithin.H13.Ch4.commutator_eq_bot_of_isComponentOf hcompG₁
      (CFSG.LieType.BorelTits.pCoreOf_le 2 (L ⊔ T))
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (L ⊔ T))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (L ⊔ T))
  have hLcent : L ⊓ pCoreOf 2 (L ⊔ T) ≤
      Subgroup.centralizer (L : Set (MulAut W)) :=
    inf_pCoreOf_le_centralizer_of_isComponent hcompG₁
  have hLQ : L ⊓ pCoreOf 2 (L ⊔ T) = ⊥ :=
    inf_pCoreOf_eq_bot_of_odd_center hcompG₁ (by
      rw [hZL, Subgroup.card_bot]
      exact odd_one)
  have hLnc : ¬ L ≤ centSub U := by
    intro hLc
    have hLQ' : L ≤ pCoreOf 2 (L ⊔ T) := by
      intro x hx
      have hx' : x ∈ (L ⊔ T) ⊓ centSub U := ⟨hLG₁ hx, hLc hx⟩
      rwa [hker] at hx'
    have : Group.IsPerfect ↥L := hLq.1
    exact Group.IsPerfect.not_isNilpotent ↥L
      ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (L ⊔ T)).to_le hLQ').isNilpotent
  set Lb : Subgroup (MulAut U) := autSub L U with hLb
  set Tb : Subgroup (MulAut U) := autSub T U with hTb
  set Gb : Subgroup (MulAut U) := autSub (L ⊔ T) U with hGb
  have hGbEq : Lb ⊔ Tb = Gb := by
    rw [hLb, hTb, hGb]
    exact (CFSG.CGT.PushingUpLit.BHS.autSub_sup hstL hstT).symm
  have hbne : bParam L (L ⊔ T) ≤ bParam Lb Gb := by
    rw [hLb, hGb]
    exact bParam_le_autSub hLG₁ hst fun k A hA hne =>
      commutator_autSub_ne_bot_of_centralizer hLG₁ hA.1 hst hker hLQcomm hLcent
        hLperf hne
  have hLbqOpen : CFSG.Open.IsQuasisimple ↥Lb := by
    rw [hLb]
    exact CFSG.Quasithin.B1Red.isQuasisimple_autSub hstL hLqopen hLnc
  have hLbq : CFSG.IsQuasisimple ↥Lb :=
    CFSG.Quasithin.A3.isQuasisimple_iff_open.mpr hLbqOpen
  have hfaith : L ⊓ centSub U = ⊥ := by
    calc L ⊓ centSub U = L ⊓ ((L ⊔ T) ⊓ centSub U) := by
          rw [← inf_assoc, inf_eq_left.mpr hLG₁]
      _ = L ⊓ pCoreOf 2 (L ⊔ T) := by rw [hker]
      _ = ⊥ := hLQ
  have hinj : Function.Injective (resHomOn U hstL) :=
    resHomOn_injective_of_faithful hstL hfaith
  let eL : ↥L ≃* ↥Lb :=
    (MonoidHom.ofInjective hinj).trans
      (MulEquiv.subgroupCongr (autSub_eq_range_resHomOn hstL).symm)
  have hZLb : Subgroup.center ↥Lb = ⊥ := by
    rw [← Subgroup.map_center_eq eL, hZL, Subgroup.map_bot]
  have hSporb : IsSpor ↥Lb .M22 := ⟨eL.symm.trans eL0⟩
  have hLbGb : Lb ≤ Gb := by
    rw [hLb, hGb]
    exact autSub_mono hLG₁ U
  have hTbGb : Tb ≤ Gb := by
    rw [hTb, hGb]
    exact autSub_mono hTG₁ U
  have hGbN : Gb ≤ Subgroup.normalizer (Lb : Set (MulAut U)) := by
    rw [hGb, hLb]
    exact CFSG.CGT.PushingUpLit.BHS.autSub_le_normalizer hG₁N
  have hLbN : (Lb.subgroupOf Gb).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer hGbN
  have hO2b : O2Trivial Gb := by
    rw [hGb]
    exact o2Trivial_autSub hw hLG₁ hTG₁ rfl hcompG₁ hTsylG₁
  have hTsylb : IsSylowIn 2 Tb Gb := by
    rw [hTb, hGb]
    exact isSylowIn_autSub hTG₁ hQleT hker hTsylG₁
  have hCbot : Subgroup.centralizer (Lb : Set (MulAut U)) ⊓ Gb = ⊥ := by
    rw [hLb, hGb]
    exact centralizer_inf_eq_bot_of_center_eq_bot hLbGb hTbGb hGbEq hGbN
      hTsylb.isPGroup hZLb hO2b
  have hCodd : Odd (Nat.card ↥(Subgroup.centralizer (Lb : Set (MulAut U)) ⊓ Gb)) := by
    rw [hCbot, Subgroup.card_bot]
    exact odd_one
  have hF : CFSG.generalizedFitting ↥Gb = Lb.subgroupOf Gb := by
    have h := CFSG.GroupTheory.generalizedFitting_sup_eq_of_isPGroup_two hLbq hLbGb hTbGb
      hLbN hTsylb.isPGroup hCodd
    rwa [hGbEq] at h
  let ρ : ↥Gb →* MulAut U := Subgroup.subtype Gb
  have hρ : Function.Injective ρ := Subgroup.subtype_injective Gb
  have hrange : ρ.range = Gb := Subgroup.range_subtype Gb
  have hO2top : pCoreOf 2 (⊤ : Subgroup ↥Gb) = ⊥ := by
    apply Subgroup.map_injective Gb.subtype_injective
    rw [CFSG.Quasithin.E1.map_subtype_pCoreOf_top Gb,
      (o2Trivial_iff_pCoreOf_eq_bot).mp hO2b, Subgroup.map_bot]
  have hmapT : (Tb.subgroupOf Gb).map ρ = Tb := Subgroup.map_subgroupOf_eq_of_le hTbGb
  have hT' : IsSylowIn 2 (Tb.subgroupOf Gb) ⊤ := by
    have h := (CFSG.Quasithin.E1.isSylowIn_subgroupOf_iff (p := 2) (P := Tb) (K := Gb)
      (H := Gb) hTbGb le_rfl).mpr hTsylb
    simpa using h
  have hfixne : fixV Tb ≠ fixV Gb := by
    rw [hTb, hGb]
    exact fixV_autSub_ne hTG₁ hQleT hfixT
  have hlt : fixV ρ.range < fixV ((Tb.subgroupOf Gb).map ρ) := by
    rw [hrange, hmapT]
    exact lt_of_le_of_ne (fixV_anti hTbGb) hfixne.symm
  let L' : Subgroup ↥Gb := Lb.subgroupOf Gb
  have hLF : L' = CFSG.generalizedFitting ↥Gb := hF.symm
  have hLq' : CFSG.IsQuasisimple ↥L' :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv
      (Subgroup.subgroupOfEquivOfLe hLbGb).symm hLbq
  have hZL' : Subgroup.center ↥L' = ⊥ := by
    have hmap := Subgroup.map_center_eq (Subgroup.subgroupOfEquivOfLe hLbGb)
    rw [hZLb] at hmap
    exact (Subgroup.map_eq_bot_iff_of_injective _
      (Subgroup.subgroupOfEquivOfLe hLbGb).injective).mp hmap
  have hSpor' : IsSporadic .M22 ↥L' := by
    obtain ⟨f⟩ := hSporb
    exact ⟨(Subgroup.subgroupOfEquivOfLe hLbGb).trans f⟩
  have hSporQ' : IsSporadic .M22 (↥L' ⧸ Subgroup.center ↥L') := by
    obtain ⟨f⟩ := hSpor'
    exact ⟨((QuotientGroup.quotientMulEquivOfEq hZL').trans
      QuotientGroup.quotientBot).trans f⟩
  have h3 : E3.aParam Gb ≤ 3 := by
    have h := CFSG.Quasithin.RonanE43.e43_M22_all U ρ hρ hO2top hT' hlt hLF hLq'
      hSporQ'
    rwa [hrange] at h
  calc bParam L Y ≤ bParam L (L ⊔ T) := hstep0
    _ ≤ bParam Lb Gb := hbne
    _ ≤ E3.aParam Gb := bParam_le_aParam
    _ ≤ 3 := h3

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
