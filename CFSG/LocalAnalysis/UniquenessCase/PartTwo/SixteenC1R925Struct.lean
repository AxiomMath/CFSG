module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1R925Defs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Fourteen3a
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22uc
public import CFSG.LocalAnalysis.UniquenessCase.UC22P20d
public import CFSG.LocalAnalysis.UniquenessCase.UCFront08
public import Certificates.Certificate2012
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TwelveLeU42O8U42
public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.OutU42Aut
public import CFSG.Adapters.LieModelSimple
public import CFSG.GroupTheory.CoprimeCentralizerCover
public import CFSG.GroupTheory.PRankCommutingSup
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3R1Aux
public import CFSG.Adapters.StatedClassicalSmallOrders
public import CFSG.ClassicalInvolution.Models.SymplecticPairs.Quadruple
public import CFSG.ClassicalInvolution.QuaternionStructure
public import CFSG.ClassicalInvolution.WeakCT.Main
public import CFSG.GH74.GLS.Defs
public import CFSG.GH74.GLS.Stage1.Thm3.Sec5.Closed
public import CFSG.GH74.GLS.Stage1.Thm3.Sec5.Statements
public import CFSG.GH74.GLS.Stage1.Thm6.Sec12.Defs
public import CFSG.GH74.GLS.Stage1.Thm6.Sec12.Ext
public import CFSG.GH74.GLS.Stage2.Final.LayerFDerive
public import CFSG.LieType.CurtisTits.Adjoint
public import CFSG.LieType.Ree.LargeReeEightTorus
public import CFSG.LieType.Ree.LargeReeInvolutionTwoCentralizers
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafOddB
public import CFSG.LocalAnalysis.ComponentClassification.ExcSelectorEvenE6
public import CFSG.LocalAnalysis.ComponentClassification.ExcSelectorEvenTriality
public import CFSG.LocalAnalysis.ComponentClassification.ExcSelectorOddE6
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeMax
public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalOddCentralizer
public import CFSG.LocalAnalysis.ComponentInitial.GL3TwoFixedModelCases
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdentLieAlt
public import CFSG.LocalAnalysis.SeitzReduction.CrossCharInputs
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotHR4
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotLeviPerp
public import CFSG.LocalAnalysis.SeitzReduction.E8PilotQ2PositionWork
public import CFSG.LocalAnalysis.SeitzReduction.E8PilotSwapLift
public import CFSG.LocalAnalysis.SeitzReduction.EPilotEndGraphE6
public import CFSG.LocalAnalysis.SeitzReduction.EPilotEndGraphTwistedXi
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotCatEvenClassical
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotCatSporadic
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotEndField
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotFieldNeighbourFix
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotFieldNeighbourLift
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotInnerField
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveWSmall
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveWSylow
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotSwapFactorNormalGraph
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotTwistedFusion
public import CFSG.LocalAnalysis.SeitzReduction.RankOneBranches
public import CFSG.LocalAnalysis.SeitzReduction.RankOneCatSL2TwoFixedA5
public import CFSG.LocalAnalysis.SeitzReduction.RankOneHypStarDef
public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotAlignImagesSwap
public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotUniqueTypeGraph
public import CFSG.LocalAnalysis.UniquenessCase.UC1K45Setup
public import CFSG.LocalAnalysis.UniquenessCase.UC1K462Inputs
public import CFSG.LocalAnalysis.UniquenessCase.UC1S4Defs462
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846d
public import CFSG.LocalAnalysis.UniquenessCase.UCInspL2Abs
public import CFSG.LocalAnalysis.UniquenessCase.UCKInputs2
public import CFSG.LocalAnalysis.UniquenessCase.UCKInputs3
public import CFSG.Quasithin.H13.QRCThreeFreeRankOneStep
public import CFSG.Quasithin.SteinbergBKHigherElementaryThompson
public import CFSG.RankThree.Chevalley.SteinbergCEF4EvenQPlusWeyl
public import CFSG.RankThree.Chevalley.SteinbergCFEvenF4PointwiseInner
public import CFSG.RankThree.Classical.SteinbergBJSymplecticSquareZeroCentralizer
public import CFSG.RankThree.PartTwo.Census.Classical.EvenUnitary

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

private theorem r925_three_le_pRank_bar2 {X : Type} [Group X] [Finite X] (h : IsU4 X 1) :
    3 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X) := by
  obtain ⟨F, hF, hFcard⟩ :=
    CFSG.LocalAnalysis.RankThreeTheoremC.TwelveLe.U42O8.UFourTwo.exists_isElemAbelian_card_27 h
  exact CFSG.SectionRank.le_pRank (by norm_num : 1 < 3) (le_top : F ≤ ⊤) hF (k := 3)
    (by rw [hFcard]; norm_num)

private theorem r925_pCore_two_not_dvd_three (L : Subgroup G) :
    ¬ 3 ∣ Nat.card (pCoreOf 2 L) := by
  intro h
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L)
  rw [hk] at h
  have h2 : 3 ∣ 2 := Nat.prime_three.dvd_of_dvd_pow h
  norm_num at h2

private theorem r925_pCore_not_dvd_three (L : Subgroup G) :
    ¬ 3 ∣ Nat.card (CFSG.pCore 2 ↥L) := by
  intro h
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 (CFSG.pCore_isPGroup (G := ↥L) (p := 2))
  rw [hk] at h
  have h2 : 3 ∣ 2 := Nat.prime_three.dvd_of_dvd_pow h
  norm_num at h2

private theorem r925_three_le_pRank_L {L : Subgroup G} (hU : IsU4 (Bar2 L) 1) :
    3 ≤ CFSG.Open.pRank 3 L := by
  have hbar := r925_three_le_pRank_bar2 hU
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hq := CFSG.SectionRank.pRank_quotient_eq (G := ↥L) (p := 3) (N := CFSG.pCore 2 ↥L)
    (r925_pCore_not_dvd_three L)
  calc 3 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (Bar2 L)) := hbar
    _ = CFSG.Open.pRank 3 (⊤ : Subgroup ↥L) := hq
    _ = CFSG.Open.pRank 3 L := (CFSG.SectionRank.pRank_eq_pRank_top_subgroup L).symm

private theorem r925_center_bar2_eq_bot {L : Subgroup G} (hU : IsU4 (Bar2 L) 1) :
    Subgroup.center (Bar2 L) = ⊥ := by
  haveI : IsSimpleGroup (Bar2 L) :=
    CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hU
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center (Bar2 L)) with h | h
  · exact h
  · exfalso
    haveI : IsMulCommutative (Bar2 L) := Subgroup.center_eq_top_iff.mp h
    have hprime : (Nat.card (Bar2 L)).Prime :=
      (Group.is_simple_iff_prime_card (α := Bar2 L)).mp inferInstance
    obtain ⟨F, _, hFcard⟩ :=
      CFSG.LocalAnalysis.RankThreeTheoremC.TwelveLe.U42O8.UFourTwo.exists_isElemAbelian_card_27 hU
    have h27 : 27 ∣ Nat.card (Bar2 L) := by
      rw [← hFcard]
      exact Subgroup.card_subgroup_dvd_card F
    rcases hprime.eq_one_or_self_of_dvd 27 h27 with h1 | h1
    · norm_num at h1
    · rw [← h1] at hprime
      norm_num at hprime

private theorem r925_commutator_zpowers_le_of_mem {A N : Subgroup G} {y : G}
    (hyN : y ∈ Subgroup.normalizer (N : Set G)) (hAy : ∀ a ∈ A, ⁅a, y⁆ ∈ N) :
    ⁅A, Subgroup.zpowers y⁆ ≤ N := by
  have hcyN : Subgroup.closure {y} ≤ Subgroup.normalizer (N : Set G) := by
    rw [← Subgroup.zpowers_eq_closure]
    exact Subgroup.zpowers_le.mpr hyN
  rw [Subgroup.commutator_le]
  intro a ha z hz
  rw [Subgroup.zpowers_eq_closure] at hz
  have hpred : ∀ w ∈ Subgroup.closure {y}, ⁅a, w⁆ ∈ N := by
    intro w hw
    induction hw using Subgroup.closure_induction with
    | mem u hu =>
      rw [show u = y from Set.mem_singleton_iff.mp hu]
      exact hAy a ha
    | one => simp
    | mul u v hu hv ihu ihv =>
      rw [commutatorElement_mul_right_eq_mul_conj,
        show ⁅a, u⁆ * u * ⁅a, v⁆ * u⁻¹ = ⁅a, u⁆ * (u * ⁅a, v⁆ * u⁻¹) by group]
      exact N.mul_mem ihu ((Subgroup.mem_normalizer_iff.mp (hcyN hu) ⁅a, v⁆).mp ihv)
    | inv u hu ihu =>
      have h1 : ⁅u, a⁆ = ⁅a, u⁆⁻¹ := by rw [commutatorElement_inv]
      rw [commutatorElement_inv_right, h1]
      simpa only [inv_inv] using
        (Subgroup.mem_normalizer_iff.mp
          ((Subgroup.normalizer (N : Set G)).inv_mem (hcyN hu)) ⁅a, u⁆⁻¹).mp (N.inv_mem ihu)
  exact hpred z hz

theorem r925_centOverO2_orderOf (D : Data G) {L : Subgroup G} (hL : L ∈ calC D.M)
    (hU : IsU4 (Bar2 L) 1) (h3 : CFSG.Open.pRank 3 D.M = 3) :
    ∀ x ∈ F08.CentOverO2 D.M L, ¬ 3 ∣ orderOf x := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro x hx hx3
  have hC3 : 3 ∣ Nat.card (F08.CentOverO2 D.M L) :=
    dvd_trans (by rw [Nat.card_zpowers]; exact hx3)
      (Subgroup.card_dvd_of_le (Subgroup.zpowers_le.mpr hx))
  obtain ⟨y, hyord⟩ := exists_prime_orderOf_dvd_card' (G := F08.CentOverO2 D.M L) 3 hC3
  have hyC : (y : G) ∈ F08.CentOverO2 D.M L := y.2
  have hyordG : orderOf (y : G) = 3 := (Subgroup.orderOf_coe y).trans hyord
  obtain ⟨hyM, hyl⟩ := mem_centOverO2_iff.mp hyC
  have hy_norm_L : (y : G) ∈ Subgroup.normalizer (L : Set G) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · rintro _ ⟨l, hl, rfl⟩
      have hmem := hyl l hl
      show (MulAut.conj (y : G)) l ∈ L
      rw [MulAut.conj_apply,
        show (y : G) * l * (y : G)⁻¹ = ((y : G) * l * (y : G)⁻¹ * l⁻¹) * l by group]
      exact L.mul_mem (CFSG.LieType.BorelTits.pCoreOf_le 2 L hmem) hl
    · rw [Subgroup.card_map_of_injective (MulAut.conj (y : G)).injective]
  have hy_norm_N : (y : G) ∈ Subgroup.normalizer (pCoreOf 2 L : Set G) :=
    UC6S846.normalizer_le_normalizer_pCoreOf L hy_norm_L
  have hcomm : ⁅L, Subgroup.zpowers (y : G)⁆ ≤ pCoreOf 2 L :=
    r925_commutator_zpowers_le_of_mem hy_norm_N (fun l hl => by
      have h := hyl l hl
      have hinv : ((y : G) * l * (y : G)⁻¹ * l⁻¹)⁻¹ ∈ pCoreOf 2 L :=
        (pCoreOf 2 L).inv_mem h
      have heq2 : ((y : G) * l * (y : G)⁻¹ * l⁻¹)⁻¹ = ⁅l, (y : G)⁆ := by
        rw [commutatorElement_def]
        group
      rwa [heq2] at hinv)
  have hfix : ∀ l : ↥L,
      UC6S846.rhoL L ⟨(y : G), hy_norm_L⟩ (QuotientGroup.mk' (CFSG.pCore 2 ↥L) l) =
        QuotientGroup.mk' (CFSG.pCore 2 ↥L) l :=
    fun l => (UC6S846.rhoL_fix_iff L ⟨(y : G), hy_norm_L⟩ l).2 (hyl l l.2)
  have hy_notin_L : (y : G) ∉ L := by
    intro hyL
    have hcen : QuotientGroup.mk' (CFSG.pCore 2 ↥L) (⟨(y : G), hyL⟩ : ↥L) ∈
        Subgroup.center (Bar2 L) := by
      rw [Subgroup.mem_center_iff]
      intro z
      obtain ⟨l, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥L) z
      have h1 : QuotientGroup.mk' (CFSG.pCore 2 ↥L)
            (Subgroup.normalizerMonoidHom L ⟨(y : G), hy_norm_L⟩ l) =
          QuotientGroup.mk' (CFSG.pCore 2 ↥L) l := by
        have := hfix l
        simpa [UC6S846.rhoL_mk] using this
      have hcoe : (Subgroup.normalizerMonoidHom L ⟨(y : G), hy_norm_L⟩ l : ↥L) =
          (⟨(y : G), hyL⟩ : ↥L) * l * (⟨(y : G), hyL⟩ : ↥L)⁻¹ := by
        apply Subtype.ext
        rw [UC6S846.rhoL_mk_coe]
        simp
      rw [hcoe] at h1
      have h3 : QuotientGroup.mk' (CFSG.pCore 2 ↥L) ((⟨(y : G), hyL⟩ : ↥L) * l) =
          QuotientGroup.mk' (CFSG.pCore 2 ↥L) l *
            QuotientGroup.mk' (CFSG.pCore 2 ↥L) (⟨(y : G), hyL⟩ : ↥L) := by
        calc QuotientGroup.mk' (CFSG.pCore 2 ↥L) ((⟨(y : G), hyL⟩ : ↥L) * l)
            = QuotientGroup.mk' (CFSG.pCore 2 ↥L)
                (((⟨(y : G), hyL⟩ : ↥L) * l * (⟨(y : G), hyL⟩ : ↥L)⁻¹) *
                  (⟨(y : G), hyL⟩ : ↥L)) := by
              congr 1
              group
          _ = QuotientGroup.mk' (CFSG.pCore 2 ↥L)
                ((⟨(y : G), hyL⟩ : ↥L) * l * (⟨(y : G), hyL⟩ : ↥L)⁻¹) *
                QuotientGroup.mk' (CFSG.pCore 2 ↥L) (⟨(y : G), hyL⟩ : ↥L) := by
              rw [map_mul]
          _ = QuotientGroup.mk' (CFSG.pCore 2 ↥L) l *
                QuotientGroup.mk' (CFSG.pCore 2 ↥L) (⟨(y : G), hyL⟩ : ↥L) := by
              rw [h1]
      simpa only [map_mul] using h3.symm
    rw [r925_center_bar2_eq_bot hU, Subgroup.mem_bot] at hcen
    have hmem : (⟨(y : G), hyL⟩ : ↥L) ∈ (QuotientGroup.mk' (CFSG.pCore 2 ↥L)).ker :=
      MonoidHom.mem_ker.mpr hcen
    rw [QuotientGroup.ker_mk'] at hmem
    have h3dvd : 3 ∣ Nat.card (CFSG.pCore 2 ↥L) := by
      have hord : orderOf (⟨(y : G), hyL⟩ : ↥L) = 3 :=
        ((Subgroup.orderOf_coe (⟨(y : G), hyL⟩ : ↥L)).symm).trans hyordG
      rw [← hord]
      exact Subgroup.orderOf_dvd_natCard (CFSG.pCore 2 ↥L) hmem
    exact r925_pCore_not_dvd_three L h3dvd
  have hy3 : (y : G) ^ 3 = 1 := by rw [← hyordG]; exact pow_orderOf_eq_one _
  have hzpel : IsElemAbelian 3 (Subgroup.zpowers (y : G)) := by
    refine ⟨inferInstance, fun z hz => ?_⟩
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hy3, one_zpow]
  obtain ⟨S, hSyl, hScent⟩ :=
    CFSG.GroupTheory.exists_isSylowOf_le_centralizer_of_commutator_le
      (p := 3) (q := 3) (X := L) (N := pCoreOf 2 L) (R := Subgroup.zpowers (y : G))
      (CFSG.LieType.BorelTits.pCoreOf_le 2 L) (Subgroup.zpowers_le.mpr hy_norm_L)
      (Subgroup.zpowers_le.mpr hy_norm_N) hzpel.isPGroup
      (r925_pCore_two_not_dvd_three L) hcomm (r925_pCore_two_not_dvd_three L)
  have hSrank : CFSG.Open.pRank 3 S = CFSG.Open.pRank 3 L :=
    CFSG.LocalAnalysis.RankThreeTheoremC.pRank_eq_of_isSylowOf3 Nat.prime_three hSyl
  have hcard1 : Nat.card (S ⊓ Subgroup.zpowers (y : G) : Subgroup G) = 1 := by
    have hdvd : Nat.card (S ⊓ Subgroup.zpowers (y : G) : Subgroup G) ∣ 3 := by
      have h : Nat.card (S ⊓ Subgroup.zpowers (y : G) : Subgroup G) ∣
          Nat.card (Subgroup.zpowers (y : G)) := Subgroup.card_dvd_of_le inf_le_right
      rwa [Nat.card_zpowers (y : G), hyordG] at h
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
    · exact h
    · exfalso
      have heq : (S ⊓ Subgroup.zpowers (y : G) : Subgroup G) = Subgroup.zpowers (y : G) :=
        Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [h, Nat.card_zpowers, hyordG])
      have hyS : (y : G) ∈ S := by
        have : (y : G) ∈ (S ⊓ Subgroup.zpowers (y : G) : Subgroup G) := by
          rw [heq]
          exact Subgroup.mem_zpowers (y : G)
        exact (Subgroup.mem_inf.mp this).1
      exact hy_notin_L (hSyl.le hyS)
  have hzp1 : 1 ≤ CFSG.Open.pRank 3 (Subgroup.zpowers (y : G)) :=
    CFSG.SectionRank.le_pRank (by norm_num : 1 < 3) le_rfl hzpel (k := 1)
      (by rw [Nat.card_zpowers, hyordG]; norm_num)
  have hsup := CFSG.GroupTheory.pRank_sup_eq_add_of_commute_of_not_dvd
    (p := 3) Nat.prime_three hScent (by rw [hcard1]; norm_num)
  have h4 : 4 ≤ CFSG.Open.pRank 3 (S ⊔ Subgroup.zpowers (y : G)) := by
    rw [hsup]
    have := r925_three_le_pRank_L hU
    omega
  have hleM : S ⊔ Subgroup.zpowers (y : G) ≤ D.M :=
    sup_le (hSyl.le.trans hL.1.le) (Subgroup.zpowers_le.mpr hyM)
  have := CFSG.SectionRank.pRank_mono (by norm_num : 1 < 3) hleM
  omega

theorem r925_calC_normal (D : Data G) {L : Subgroup G} (hL : L ∈ calC D.M)
    (hU : IsU4 (Bar2 L) 1) (h : ∀ x ∈ F08.CentOverO2 D.M L, ¬ 3 ∣ orderOf x) :
    (L.subgroupOf D.M).Normal := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer hL.1.le]
  intro m hm
  by_contra hmn
  have hK : uniqueFourConj m L ∈ calC D.M :=
    uc22p22u_calC_conj (Subgroup.le_normalizer) hL hm
  have hne : L ≠ uniqueFourConj m L :=
    fun heq => hmn (UC6.uniqueFourConj_eq_self_iff.mp heq.symm)
  have hcomm : ⁅L, uniqueFourConj m L⁆ ≤ pCoreOf 2 L :=
    fun x hx => (Subgroup.mem_inf.mp (calC_commutator_le_of_ne hL hK hne hx)).1
  have hKcent : uniqueFourConj m L ≤ F08.CentOverO2 D.M L := by
    intro k hk
    rw [mem_centOverO2_iff]
    refine ⟨hK.1.le hk, fun l hl => ?_⟩
    have hmem : ⁅k, l⁆ ∈ ⁅uniqueFourConj m L, L⁆ :=
      Subgroup.commutator_mem_commutator hk hl
    have hcommKL : ⁅uniqueFourConj m L, L⁆ ≤ pCoreOf 2 L := by
      rw [Subgroup.commutator_comm]
      exact hcomm
    exact hcommKL hmem
  have h3K : 3 ∣ Nat.card (uniqueFourConj m L) := by
    have hU' : IsU4 (Bar2 (uniqueFourConj m L)) 1 := by
      obtain ⟨e⟩ := uc22p20d_bar2_conj m⁻¹ L
      exact CFSG.Blueprint.LieModel.of_mulEquiv e hU
    obtain ⟨F, _, hFcard⟩ :=
      CFSG.LocalAnalysis.RankThreeTheoremC.TwelveLe.U42O8.UFourTwo.exists_isElemAbelian_card_27 hU'
    have hdvd : Nat.card F ∣ Nat.card (Bar2 (uniqueFourConj m L)) :=
      Subgroup.card_subgroup_dvd_card F
    rw [hFcard] at hdvd
    exact (show 3 ∣ 27 by norm_num).trans (hdvd.trans
      (Subgroup.card_quotient_dvd_card (CFSG.pCore 2 ↥(uniqueFourConj m L))))
  obtain ⟨xK, hxKord⟩ := exists_prime_orderOf_dvd_card' (G := uniqueFourConj m L) 3 h3K
  have hxKmem : (xK : G) ∈ F08.CentOverO2 D.M L := hKcent xK.2
  have hxKordG : orderOf (xK : G) = 3 := (Subgroup.orderOf_coe xK).trans hxKord
  exact h (xK : G) hxKmem (by rw [hxKordG])

theorem r925_exists_normal_quot (D : Data G) {L : Subgroup G}
    (hn : (L.subgroupOf D.M).Normal) (hU : IsU4 (Bar2 L) 1)
    (hLM : L ≤ D.M := by exact hL.1.le) :
    ∃ C : Subgroup ↥D.M, C.Normal ∧ (∀ x ∈ C, (x : G) ∈ F08.CentOverO2 D.M L) ∧
      Nat.card (↥D.M ⧸ C) ∣ 51840 := by
  have hMN : D.M ≤ Subgroup.normalizer (L : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLM).mp hn
  let ρ : ↥D.M →* MulAut (Bar2 L) :=
    (UC6S846.rhoL L).comp (Subgroup.inclusion hMN)
  refine ⟨ρ.ker, inferInstance, ?_, ?_⟩
  · intro x hx
    rw [mem_centOverO2_iff]
    refine ⟨x.2, fun l hl => ?_⟩
    have hx1 : UC6S846.rhoL L (Subgroup.inclusion hMN x) = 1 := by
      have := MonoidHom.mem_ker.mp hx
      simpa [ρ] using this
    exact (UC6S846.rhoL_fix_iff L (Subgroup.inclusion hMN x) ⟨l, hl⟩).1 (by rw [hx1]; rfl)
  · have hcard : Nat.card (↥D.M ⧸ ρ.ker) = Nat.card ρ.range :=
      Nat.card_congr (QuotientGroup.quotientKerEquivRange ρ).toEquiv
    rw [hcard]
    exact (Subgroup.card_subgroup_dvd_card ρ.range).trans (by
      rw [(CFSG.EvenSporadicStandard.M22Std.card_mulAut_of_lieModel_psu42 hU).1])

theorem r925_kGroupNonab_of_kernel {X : Type} [Group X] [Finite X] (C : Subgroup X) [C.Normal]
    (hC : ∀ x ∈ C, ¬ 3 ∣ orderOf x) (hq : Nat.card (X ⧸ C) ∣ 51840) :
    CFSG.KCore.KGroupNonab (DvdOrThreeFree 51840) X := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro K L hLK hLnorm hsimple hnonab
  let mk : ↥K →* (↥K ⧸ L.subgroupOf K) := QuotientGroup.mk' (L.subgroupOf K)
  let D : Subgroup ↥K := (K ⊓ C).subgroupOf K
  let N : Subgroup (↥K ⧸ L.subgroupOf K) := D.map mk
  have hmksurj : Function.Surjective mk := QuotientGroup.mk'_surjective _
  have hDeq : D = C.subgroupOf K := by
    ext x
    simp only [D, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    exact ⟨fun hx => hx.2, fun hx => ⟨x.2, hx⟩⟩
  have hDnorm : D.Normal := by
    rw [hDeq]
    exact Subgroup.Normal.subgroupOf (inferInstance : C.Normal) K
  have hNnorm : N.Normal := Subgroup.Normal.map hDnorm mk hmksurj
  haveI := hNnorm
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with hN | hN
  ·
    left
    have hle : D ≤ L.subgroupOf K := by
      intro x hx
      have hxN : mk x ∈ N := Subgroup.mem_map_of_mem mk hx
      rw [hN, Subgroup.mem_bot] at hxN
      exact (QuotientGroup.eq_one_iff x).mp hxN
    have hleker : D ≤ mk.ker := by
      rw [QuotientGroup.ker_mk']
      exact hle
    let q : (↥K ⧸ D) →* (↥K ⧸ L.subgroupOf K) := QuotientGroup.lift (N := D) mk hleker
    have hqsurj : Function.Surjective q :=
      QuotientGroup.lift_surjective_of_surjective (N := D) (φ := mk) (hφ := hmksurj)
        (HN := hleker)
    have hdiv1 : Nat.card (↥K ⧸ L.subgroupOf K) ∣ Nat.card (↥K ⧸ D) :=
      Subgroup.card_dvd_of_surjective (f := q) hqsurj
    let φ : ↥K →* (X ⧸ C) := (QuotientGroup.mk' C).comp K.subtype
    have hker : φ.ker = D := by
      ext x
      simp only [MonoidHom.mem_ker, φ, MonoidHom.comp_apply, Subgroup.subtype_apply,
        QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, D, Subgroup.mem_subgroupOf,
        Subgroup.mem_inf]
      exact ⟨fun hx => ⟨x.2, hx⟩, fun hx => hx.2⟩
    have hdiv2 : Nat.card (↥K ⧸ D) ∣ Nat.card (X ⧸ C) := by
      rw [← hker, Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv]
      exact Subgroup.card_subgroup_dvd_card φ.range
    exact (hdiv1.trans hdiv2).trans hq
  ·
    right
    have hmapdvd : Nat.card N ∣ Nat.card D := Subgroup.card_map_dvd D mk
    have hDcard : Nat.card D = Nat.card (K ⊓ C : Subgroup X) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
    have himg : Nat.card (↥K ⧸ L.subgroupOf K) = Nat.card N := by
      rw [hN, Subgroup.card_top]
    have hdiv : Nat.card (↥K ⧸ L.subgroupOf K) ∣ Nat.card (K ⊓ C : Subgroup X) := by
      rw [himg]
      exact hDcard ▸ hmapdvd
    have hC3 : ¬ 3 ∣ Nat.card (K ⊓ C : Subgroup X) := by
      intro hdvd
      obtain ⟨c, hcord⟩ := exists_prime_orderOf_dvd_card' (G := (K ⊓ C : Subgroup X)) 3 hdvd
      exact hC (c : X) (Subgroup.mem_inf.mp c.2).2
        (by rw [Subgroup.orderOf_coe c, hcord])
    intro hdvd
    exact hC3 (hdvd.trans hdiv)

theorem r925_m_catalogue (D : Data G) {L : Subgroup G}
    (hL : L ∈ calC D.M) (hU : IsU4 (Bar2 L) 1) (h3 : CFSG.Open.pRank 3 D.M = 3) :
    CFSG.KCore.KGroupNonab (DvdOrThreeFree 51840) ↥D.M := by
  have h := r925_centOverO2_orderOf D hL hU h3
  obtain ⟨C, hC, hCc, hCq⟩ := r925_exists_normal_quot D (r925_calC_normal D hL hU h) hU
  haveI := hC
  exact r925_kGroupNonab_of_kernel C
    (fun x hx => by rw [← Subgroup.orderOf_coe]; exact h _ (hCc x hx)) hCq

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
