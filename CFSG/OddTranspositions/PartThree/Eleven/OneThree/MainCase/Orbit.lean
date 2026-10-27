module

public import CFSG.OddTranspositions.PartThree.Eleven.OneThree.MainCase.Element
import CFSG.GroupTheory.OddConjInvCommute
import CFSG.OddTranspositions.PartThree.Eleven.OneThree.MainCase.GoodCase
import CFSG.OddTranspositions.PartThree.Eleven.OneThree.MainCase.BadCase
import CFSG.OddTranspositions.SevenFourEight.ImageConnectedThree
import CFSG.CGT.Timmesfeld75.Statements
import CFSG.CGT.Timmesfeld75.Targets
import CFSG.Fischer.NoF25.Local
import CFSG.GroupTheory.Fitting.LayerTopBot
import CFSG.GroupTheory.PerfectLeOfPGroupQuotient
import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitBenderInvUnitary
import CFSG.LocalAnalysis.ComponentClassification.RankTwoBenderAutE4Unitary
import CFSG.OddTranspositions.AlmostSimple
import CFSG.OddTranspositions.Disconnected
import CFSG.OddTranspositions.TheoremTwo.ImageConnected
import CFSG.OddTranspositions.WreathQuotient
import CFSG.Sporadic.Th.Max3.Data
import CFSG.Timmesfeld.Transvection.Statement

public section

namespace CFSG.OddTranspositions.PartThree.ElevenThree

open CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72 CFSG.Timmesfeld.Connectivity
open CFSG.OddTranspositions.QZ
open CFSG.OddTranspositions.PartFour

variable {G : Type} [Group G] [Finite G] {D : Set G}

private theorem odd_orderOf_of_mem_rBlock {ε : Set G} {x : G} (hx : x ∈ rBlock D ε) :
    Odd (orderOf x) := by
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
  have h := (CFSG.ABGLocalTools.odd_card_oddCore (H := Halpha D ε)).of_dvd_nat
    (Subgroup.orderOf_dvd_natCard _ hy)
  simpa [Subgroup.orderOf_coe] using h

private theorem mk_eq_one_of_relations {X : Type*} [Group X] [Finite X] {M : Subgroup X}
    [M.Normal] {N : Subgroup (X ⧸ M)} (hN : Odd (Nat.card N)) {a x : X}
    (ha : a * a = 1) (hinv : a * x * a = x⁻¹)
    (hcomm : Commute (QuotientGroup.mk' M a) (QuotientGroup.mk' M x))
    (hxN : QuotientGroup.mk' M x ∈ N) : QuotientGroup.mk' M x = 1 := by
  have hqainv : QuotientGroup.mk' M a * QuotientGroup.mk' M a = 1 := by
    rw [← map_mul, ha, map_one]
  have hqxinv : QuotientGroup.mk' M a * QuotientGroup.mk' M x * QuotientGroup.mk' M a =
      (QuotientGroup.mk' M x)⁻¹ := by
    have h := congrArg (QuotientGroup.mk' M) hinv
    simpa only [map_mul, map_inv] using h
  have hodd : Odd (orderOf (QuotientGroup.mk' M x)) :=
    hN.of_dvd_nat (Subgroup.orderOf_dvd_natCard N hxN)
  refine CFSG.GroupTheory.eq_one_of_odd_of_conj_eq_inv_of_commute hodd ?_ hcomm.eq
  rw [inv_eq_of_mul_eq_one_right hqainv]
  exact hqxinv


namespace MainHyp

variable {hC : HypothesisC D}

private theorem dalphaStar_conj_mem_oddLineImage (h : MainHyp hC) {ε : Set G}
    (hε : ε ∈ Dalpha D hC.alpha) {c : Halpha D hC.alpha} (hc : (c : G) ∈ ε)
    {hY : HypothesisC (imageClass hC)}
    (hYd : hY.d = QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) c) :
    ∀ t ∈ DalphaStar (imageClass hC) hY.alpha,
      ∀ n ∈ oddLineImage hC ε, t * n * t⁻¹ ∈ oddLineImage hC ε := by
  intro t ht n hn
  have htE : t ∈ imageClass hC := DalphaStar_subset hY.isBlock_alpha ht
  have htcomm : Commute t hY.d := (hY.DalphaStar_subset_commute ht).2
  exact conj_mem_oddLineImage h hε hc t htE (by rwa [hYd] at htcomm) n hn

theorem commute_mk_of_mem (h86 : Lemma8_6) (h87 : Theorem8_7) (h : MainHyp hC)
    (hIH : Theorem11_3Below (Nat.card G)) (hconn : ¬ Disconnected (imageClass hC))
    {δ ε : Set G} (hδ : δ ∈ Dalpha D hC.alpha) (hε : ε ∈ Dalpha D hC.alpha)
    (hεδ : ε ∈ Dalpha D δ) {a : Halpha D hC.alpha} (ha : (a : G) ∈ δ) :
    ∀ n ∈ oddLineImage hC ε,
      Commute (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) a) n := by
  classical
  obtain ⟨c, hcε⟩ := nonempty_of_mem_blockClass hC.isBlock_alpha.nonempty hε.1
  have hcStar : c ∈ DalphaStar D hC.alpha := subset_DalphaStar hε hcε
  let cH : Halpha D hC.alpha := ⟨c, Subgroup.subset_closure hcStar⟩
  have hcHε : (cH : G) ∈ ε := hcε
  have hcbar : QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) cH ∈
      imageClass hC := ⟨cH, hcStar, rfl⟩
  obtain ⟨hY, hYd⟩ := exists_hypothesisC_imageClass h hconn hcbar
  have haStar : (a : G) ∈ DalphaStar D hC.alpha := subset_DalphaStar hδ ha
  have hcommG : Commute (a : G) c := hεδ.2.2.2 (a : G) ha c hcε
  have hcommH : Commute a cH := Subtype.ext hcommG.eq
  have hcomm : Commute (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) a)
      (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) cH) :=
    hcommH.map (QuotientGroup.mk' _)
  have hne : QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) a ≠
      QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) cH :=
    mk_ne_mk_of_mem_Dalpha h hδ hε hεδ ha hcHε
  have hunion : QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) a ∈
      hY.alpha ∪ DalphaStar (imageClass hC) hY.alpha ∪
        AalphaStar (imageClass hC) hY.alpha := by
    rw [← hY.eq_alpha_union]
    exact ⟨a, haStar, rfl⟩
  have hle : oddLineImage hC ε ≤ Subgroup.closure (commSet (imageClass hC) hY.d) := by
    rw [hYd]
    exact oddLineImage_le_closure_commSet h hε hcHε
  have hnorm := dalphaStar_conj_mem_oddLineImage h hε hcHε hYd
  rcases hunion with (haα | haDstar) | haAstar
  · have hnorm' : ∀ t ∈ centSet (imageClass hC) hY.d,
        ∀ n ∈ oddLineImage hC ε, t * n * t⁻¹ ∈ oddLineImage hC ε := by
      rintro t ⟨htE, htcomm⟩ n hn
      exact conj_mem_oddLineImage h hε hcHε t htE (by rwa [hYd] at htcomm) n hn
    have hdN : ∀ n ∈ oddLineImage hC ε, Commute hY.d n := by
      intro n hn
      rw [hYd]
      exact commute_mk_of_mem_oddLineImage (hC := hC) (ε := ε) (c := cH) hcHε n hn
    have had : QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) a ≠ hY.d := by
      rwa [hYd]
    have hcomm' : Commute (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) a)
        hY.d := by
      rwa [← hYd] at hcomm
    exact commute_of_mem_alpha_of_commute h86 h87 hY
      (CFSG.OddTranspositions.solvable_normal_eq_bot_imageClass hC)
      (odd_card_oddLineImage ε) hle hnorm' hdN haα had hcomm'
  · exact commute_of_mem_DalphaStar_of_odd hY
      (map_solvableRadical_eq_center_imageClass h hIH hY)
      (odd_card_oddLineImage ε) hle hnorm haDstar
  · rw [hY.AalphaStar_eq_diff_alpha] at haAstar
    exact (haAstar.1.2 (by rwa [← hYd] at hcomm)).elim

private theorem exists_mk_mul_conj_eq_one (h86 : Lemma8_6) (h87 : Theorem8_7)
    (h : MainHyp hC) (hIH : Theorem11_3Below (Nat.card G))
    (hconn : ¬ Disconnected (imageClass hC)) {δ ε : Set G}
    (hδ : δ ∈ Dalpha D hC.alpha) (hε : ε ∈ Dalpha D hC.alpha)
    (hεδ : ε ∈ Dalpha D δ) {k a : G} (hk : k ∈ kBlock D ε) (ha : a ∈ δ) :
    ∃ (xH : Halpha D hC.alpha) (s : G),
      (xH : G) = a * (k * a * k⁻¹) ∧
      s ∈ Subgroup.zpowers (a * (k * a * k⁻¹)) ∧
      s * a * s⁻¹ = k * a * k⁻¹ ∧
      s ∈ kBlock D hC.alpha := by
  obtain ⟨⟨hxr, hxL⟩, s, hs, hsa⟩ :=
    mul_conj_mem_rBlock_inf_lineGroup h hδ hε hεδ hk ha
  have hxH : a * (k * a * k⁻¹) ∈ Halpha D hC.alpha :=
    Subgroup.closure_mono
      (Set.inter_subset_left : DalphaStar D hC.alpha ∩ DalphaStar D ε ⊆
        DalphaStar D hC.alpha) hxL
  let xH : Halpha D hC.alpha := ⟨a * (k * a * k⁻¹), hxH⟩
  let aH : Halpha D hC.alpha :=
    ⟨a, Subgroup.subset_closure (subset_DalphaStar hδ ha)⟩
  have hxbar : QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) xH ∈
      oddLineImage hC ε := by
    rw [oddLineImage]
    refine Subgroup.mem_map.mpr ⟨xH, ?_, rfl⟩
    rw [Subgroup.mem_subgroupOf]
    exact ⟨hxr, hxL⟩
  have hxcomm : Commute (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) aH)
      (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) xH) :=
    (commute_mk_of_mem h86 h87 h hIH hconn hδ hε hεδ (a := aH) ha) _ hxbar
  have ha2 : a * a = 1 := hC.setup.oddT.mul_self_eq_one (hδ.2.1 ha)
  have hb2 : (k * a * k⁻¹) * (k * a * k⁻¹) = 1 := by
    have h := congrArg (fun z => k * z * k⁻¹) ha2
    simpa [mul_assoc] using h
  have hainv : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha2
  have hbinv : (k * a * k⁻¹)⁻¹ = k * a * k⁻¹ :=
    inv_eq_of_mul_eq_one_right hb2
  have haH2 : aH * aH = 1 := Subtype.ext ha2
  have hxinv : aH * xH * aH = xH⁻¹ := by
    apply Subtype.ext
    calc a * (a * (k * a * k⁻¹)) * a
        = (a * a) * (k * a * k⁻¹) * a := by group
      _ = (k * a * k⁻¹) * a := by rw [ha2, one_mul]
      _ = (a * (k * a * k⁻¹))⁻¹ := by rw [mul_inv_rev, hbinv, hainv]
  have hqx1 : QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) xH = 1 :=
    mk_eq_one_of_relations (odd_card_oddLineImage ε) haH2 hxinv hxcomm hxbar
  have hxM : xH ∈ CFSG.solvableRadical (Halpha D hC.alpha) :=
    (QuotientGroup.eq_one_iff xH).mp hqx1
  have hxodd : Odd (orderOf xH) := by
    rw [← Subgroup.orderOf_coe]
    exact odd_orderOf_of_mem_rBlock hxr
  have hxK : xH ∈ EightOne.twoOddCore (Halpha D hC.alpha) :=
    mem_twoOddCore_of_mem_solvableRadical h hxM hxodd
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hs
  have hsK : s ∈ kBlock D hC.alpha := by
    rw [← hn]
    exact Subgroup.mem_map.mpr ⟨xH ^ n, zpow_mem hxK n, rfl⟩
  exact ⟨xH, s, rfl, hs, hsa, hsK⟩

theorem kOrbit_subset (h86 : Lemma8_6) (h87 : Theorem8_7) (h : MainHyp hC)
    (hIH : Theorem11_3Below (Nat.card G)) (hconn : ¬ Disconnected (imageClass hC))
    {δ ε : Set G} (hδ : δ ∈ Dalpha D hC.alpha) (hε : ε ∈ Dalpha D hC.alpha)
    (hεδ : ε ∈ Dalpha D δ) : kOrbit D ε δ ⊆ kOrbit D hC.alpha δ := by
  intro z hz
  obtain ⟨k, hk, rfl⟩ := hz
  obtain ⟨a, ha⟩ := nonempty_of_mem_blockClass hC.isBlock_alpha.nonempty hδ.1
  obtain ⟨_xH, s, _hxeq, _hs, hsa, hsK⟩ :=
    exists_mk_mul_conj_eq_one h86 h87 h hIH hconn hδ hε hεδ hk ha
  have hkclass : cimg k δ ∈ blockClass hC.alpha := cimg_mem_blockClass_iff.mpr hδ.1
  have hsclass : cimg s δ ∈ blockClass hC.alpha := cimg_mem_blockClass_iff.mpr hδ.1
  have hks : cimg s δ = cimg k δ := by
    refine eq_of_mem_of_mem_blockClass hC.isBlock_alpha hsclass hkclass
      ⟨k * a * k⁻¹, ?_, ?_⟩
    · rw [← hsa]
      exact ⟨a, ha, rfl⟩
    · exact ⟨a, ha, rfl⟩
  exact ⟨s, hsK, hks⟩

theorem kOrbit_eq (h86 : Lemma8_6) (h87 : Theorem8_7) (h : MainHyp hC)
    (hIH : Theorem11_3Below (Nat.card G)) (hconn : ¬ Disconnected (imageClass hC))
    {β γ : Set G} (hβ : β ∈ Dalpha D hC.alpha) (hγ : γ ∈ Dalpha D hC.alpha)
    (hγβ : γ ∈ Dalpha D β) : kOrbit D γ hC.alpha = kOrbit D β hC.alpha := by
  classical
  have hsymm : ∀ {η₁ η₂ : Set G}, η₁ ∈ Dalpha D hC.alpha → η₂ ∈ Dalpha D hC.alpha →
      η₂ ∈ Dalpha D η₁ → kOrbit D η₂ hC.alpha ⊆ kOrbit D η₁ hC.alpha := by
    intro η₁ η₂ hη₁ hη₂ hη₂η₁
    obtain ⟨g, hg⟩ := mem_blockClass_iff.mp hη₁.1
    let hC' : HypothesisC D := hC.conj g
    have hα' : hC'.alpha = η₁ := (HypothesisC.conj_alpha hC g).trans hg.symm
    have h' : MainHyp hC' := h.conj g
    have hconn' : ¬ Disconnected (imageClass hC') :=
      not_disconnected_imageClass_conj hconn g
    have hδ : hC.alpha ∈ Dalpha D hC'.alpha := by
      rw [hα']
      exact mem_Dalpha_symm hη₁ hC.isBlock_alpha.subset
    have hε : η₂ ∈ Dalpha D hC'.alpha := by rwa [hα']
    have hsub := kOrbit_subset h86 h87 h' hIH hconn' hδ hε hη₂
    rwa [hα'] at hsub
  exact Set.Subset.antisymm
    (hsymm hβ hγ hγβ)
    (hsymm hγ hβ (mem_Dalpha_symm hγβ hβ.2.1))

end MainHyp

end CFSG.OddTranspositions.PartThree.ElevenThree
