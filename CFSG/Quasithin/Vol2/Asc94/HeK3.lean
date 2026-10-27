module

public import CFSG.Quasithin.Vol2.Asc94.HeK2
public import CFSG.Sporadic.Th.Max3.Core

public section

namespace CFSG.Quasithin.A94

open Subgroup CFSG.CGT.Timmesfeld75 CFSG.CGT.M24S CFSG.Open CFSG.Blueprint
open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoStandard CFSG.ComponentClassification.RankTwoL3Four
open CFSG.ComponentClassification CFSG.ComponentClassification.AS81
open CFSG.Blueprint.NativeSporadic


theorem heCaseIIK_of_geometry {d : L34E16Cert}
    (hE16 : RankTwoL3Four.HypII.l34CheckWE16 d = true) (h11 : Step11)
    (h4 : AS76b.Asc75Theorem4) (h34 : AS76b.Asc08Lemma34) (hII : L34HypII)
    (hGeo : HeGeometryStmt) : HeCaseIIK := by
  intro hF6 G _ _ z e hs hK S h1 h2
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hz : orderOf z = 2 := S.ord
  obtain ⟨A, R, g, hstd, hL, hRA, hRsyl, hRe, hR4, hEA, hFA, hRE, hRF, hgn, hcomm, hconj,
    hEF, hEFc, hsyl⟩ := hGeo hF6 G z e hs hK S h1 h2
  have hAbot : A ≠ ⊥ := by
    intro h
    have h1 := card_rankTwoQuot_of_typeL34 hL
    have h2 : Nat.card (rankTwoQuot A) = 1 := by
      subst h
      exact Nat.card_of_subsingleton (1 : rankTwoQuot (⊥ : Subgroup G))
    omega
  have hRC : R ≤ centralizer (A : Set G) := hRsyl.le
  have hAnn : ¬ A.Normal := fun hAn =>
    hgn (by rw [Subgroup.normalizer_eq_top_iff.mpr hAn]; exact Subgroup.mem_top g)
  have hrank : 2 ≤ Open.pRank 2 (centralizer (A : Set G)) := by
    have := CFSG.SectionRank.le_pRank one_lt_two hRC hRe (k := 2) (by rw [hR4]; norm_num)
    exact this
  have hodd : standardComponentOddCore G = ⊥ := by
    refine sSup_eq_bot.mpr fun N ⟨hNn, hNodd⟩ => ?_
    haveI := hNn
    rcases hs.eq_bot_or_eq_top_of_normal N with h | h
    · exact h
    · exfalso
      have h2 : 2 ∣ Nat.card G := hz ▸ orderOf_dvd_natCard z
      rw [h, Subgroup.card_top] at hNodd
      have := Nat.odd_iff.mp hNodd
      omega
  have hBase : Base G A :=
    ⟨(⟨hK, hstd, hAnn, hrank⟩ : RankTwoHyp G A).toNF, hodd, hII A hstd.1.1 hL, Or.inl hL⟩
  have hEelem : IsElemAbelian 2 (tr e L52.A1) := isElemAbelian_tr e L52.isElemAbelian_A1
  have hFelem : IsElemAbelian 2 (tr e L52.A2) := isElemAbelian_tr e L52.isElemAbelian_A2
  have hEcard : Nat.card (tr e L52.A1) = 64 := by rw [card_tr, L52.card_A1]; norm_num
  have hFcard : Nat.card (tr e L52.A2) = 64 := by rw [card_tr, L52.card_A2]; norm_num
  have hBcard : Nat.card ↥(tr e L52.A1 ⊓ tr e L52.A2) = 16 := by
    rw [← tr_inf, card_tr, L52.card_A1_inf_A2]; norm_num
  have hne : tr e L52.A1 ≠ tr e L52.A2 := by
    intro h
    rw [h, inf_idem, hFcard] at hBcard
    omega
  have hRA' : A ⊔ R = A := sup_eq_left.mpr hRA
  have hFrame : Frame G A A R g (tr e L52.A1) (tr e L52.A2) :=
    { base := hBase
      le := le_rfl
      quasisimple := hstd.1
      typeA₁ := hL
      sylowR := hRsyl
      elemR := hRe
      cardR := hR4
      not_mem := hgn
      comm := hcomm
      conj_le := by rw [hRA']; exact hconj
      E_le := by rw [hRA']; exact hEA
      F_le := by rw [hRA']; exact hFA
      R_le_E := hRE
      R_le_F := hRF
      elemE := hEelem
      elemF := hFelem
      cardE := hEcard
      cardF := hFcard
      ne := hne
      inf_eq := hEF
      inf_eq_center := hEFc
      sylow := by rw [hRA']; exact hsyl }
  have heven : Even (Nat.card (center ↥A)) := by
    have hle : R.subgroupOf A ≤ center ↥A := by
      intro x hx
      rw [mem_center_iff]
      intro a
      apply Subtype.ext
      exact (mem_centralizer_iff.mp (hRC (mem_subgroupOf.mp hx)) a a.2)
    have h4 : Nat.card (R.subgroupOf A) = 4 := by
      rw [Nat.card_congr (subgroupOfEquivOfLe hRA).toEquiv, hR4]
    have := Subgroup.card_dvd_of_le hle
    rw [h4] at this
    exact even_iff_two_dvd.mpr (dvd_trans (by norm_num) this)
  have htop : rankTwoX A ⊔ R = ⊤ := by
    haveI : (rankTwoX A).Normal := Subgroup.normalClosure_normal
    rcases hs.eq_bot_or_eq_top_of_normal (rankTwoX A) with h | h
    · exfalso
      apply hAbot
      refine eq_bot_iff.mpr fun a ha => ?_
      have : a ∈ rankTwoX A := Subgroup.subset_normalClosure (s := (A : Set G)) ha
      rw [h] at this
      exact this
    · rw [h, top_sup_eq]
  have hset : Sec4SettingNB G A R g (tr e L52.A1) (tr e L52.A2) := ⟨hFrame, hL, heven, htop⟩
  have hQ : Sec4QNB G A R g (tr e L52.A1) (tr e L52.A2) (tr e L52.Tm) (tr e L52.Qh) z :=
    { setting := hset
      sylowN := HeK.isSylowOf_T_normalizer_J e hF6 S h1 h2
      sylow := HeK.isSylowOf_T_top e hz
      le := HeK.Q_le_T e
      extraspecial := HeK.isExtraspecial_Q e
      card := HeK.card_Q e
      order_z := hz
      center_Q := HeK.centerIn_Q e hz
      center_S₁ := HeK.centerIn_T e hz
      normE := (HeK.Q_le_T e).trans (HeK.T_le_normalizer_A1 e hz hF6)
      normF := (HeK.Q_le_T e).trans (HeK.T_le_normalizer_A2 e hz hF6)
      lt := HeK.lt_card_Q_T e }
  have h44 := step44iiNB_of hE16 h11
  have hNX := sec4NXModelNB_of hE16 h11 (sec4NXKernelNB_of h4 h34 hE16 h11)
  have h46 := step46NB_of h44 hNX G A R g _ _ _ _ z hQ
  have hS₁ : ∃ P : Sylow 2 (Carrier .He), Nonempty (tr e L52.Tm ≃* P) := by
    rcases h44 G A R g _ _ hset (tr e L52.Tm) hQ.sylowN with ⟨-, hP⟩ | ⟨hc, -⟩
    · exact hP
    · exfalso
      rw [HeK.card_T e] at hc
      norm_num at hc
  exact sec4HeCaseNB_of hE16 h11 G A R g _ _ _ _ z hQ hs (HeK.pCoreOf_Cz e) h46.1
    (hNX G A R g _ _ hset) hS₁ (HeK.nonempty_iso_cornerTransvection e)

end CFSG.Quasithin.A94
