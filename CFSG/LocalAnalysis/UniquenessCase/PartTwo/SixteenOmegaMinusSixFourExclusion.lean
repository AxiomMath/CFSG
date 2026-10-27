module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1677ThreeDefs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenOmegaMinusSixFourStrong
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenOmegaMinusSixFourThreeCentralizer
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenOmegaMinusSixNaturalField
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenStdSevenDonors
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight102R8103
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight106Holds
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight102Syl3Holds
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight102U45KeyHolds
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight102SylOddHolds
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight102KTypesHolds
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight102U45OutHolds
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight102TorusFixHolds
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight102AltTenHolds
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight102U45AltFiveHolds
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KStrongEmbedded72Holds
import CFSG.LieType.BorelTits.Basic
public import Certificates.Certificate431004
public import Certificates.Certificate17430
public import Certificates.Certificate9726
import CFSG.GH74.GLS.IVK.Proofs2.Ivk73G4U3Out
import CFSG.GH74.GLS.IVK.Proofs2.Ivk93Cfg2
import CFSG.GH74.GLS.IVK.Proofs2.Ivk93Field
import CFSG.GH74.GLS.IVK.Proofs2.Ivk93PGU
import CFSG.GH74.GLS.IVK.Proofs2.Ivk93WPGU
import CFSG.GroupTheory.Fitting.LayerContainment
import CFSG.GroupTheory.RegularModuleThree
import CFSG.LocalAnalysis.AGLEmbedding.OneLieCompetitor
import CFSG.LocalAnalysis.AGLEmbedding.OneLieNormalClosure
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIaBlock
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIbThreeMSide
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallPosA
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallPosT
import CFSG.LocalAnalysis.GLTheoremA.CatA.YS1011I1416Small
import CFSG.LocalAnalysis.GLTheoremA.S11.InputsCE
import CFSG.LocalAnalysis.GLTheoremA.S11.InputsElim
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ICitedHyp111K
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81NineSeventeenReduction
import CFSG.LocalAnalysis.RankThreeTheoremC.AGLHyp111NineThree
import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseOne3ACz
import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseOne3AFi22
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15LiftCore
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15SecRank
import CFSG.LocalAnalysis.RankThreeUC.GN15FFOLink
import CFSG.LocalAnalysis.RankThreeUC.GN15FFOLinkPSL
import CFSG.LocalAnalysis.RankThreeUC.GN15JOutOdd
import CFSG.Quasithin.Background.SmithB42L2L32
import CFSG.Quasithin.Background.SmithB42L2Nat
import CFSG.Quasithin.Background.SmithB51LnRealB
import CFSG.Quasithin.SteinbergBNA7ThreeRankClosure
import Certificates.Certificate9681

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

variable {G : Type} [Group G] [Finite G]

section


theorem s168e3_false_of_omegaMinus_six_four_natural
    {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV)
    (hs : s15 D.M V₀ V hV L = 1)
    (hN : NatOmegaMinus (lBar V₀ V hV L) (wTil V₀ V hV L) ⊥ 6 2) : False := by
  have hPair := c.setting.hyp16.hyp125.pairFacts
  have hnotSP : ¬ IsStronglyPEmbedded 3 D.M := fun hSP =>
    s168e3_false_of_omegaMinus_six_four_natural_of_stronglyThreeEmbedded c hs hN hSP
  have hsig : D.sig = {5} :=
    (s168e3_sig_eq_five_of_omegaMinus_six_four_natural c hs hN).1
  have h5 : 5 ∈ D.sig := by
    rw [hsig]
    exact Set.mem_singleton 5
  obtain ⟨K, P, B, hKc, _hnormK, _hbarK, hU4K, hP, _hBK, hB, hfixV⟩ :=
    s168e3_exists_three_centralizer_fixed_omegaMinus_six_four D c hs hN
  have hH : F08.Hyp8102 D K P 5 2 := ⟨hKc, Or.inr hU4K, hnotSP, h5, hP⟩
  have h614 : UC6.R6_14 D := r6_14_of_s168e3Std c.std
  have h76 : F07.R76Sig D := r76Sig_of_s168e3Std c.std
  have h72 : F07.R72 D := r72_of_s168e3Std c.std
  have h8103 : R8103At D K P 5 2 :=
    r8103_at_of_even D c.std.hSg c.std.h3 h614 h76 h72
      UC22.kStrongEmbedded72_holds kU45Syl3_holds kU45Key_holds
      kU4SylOdd_holds kU45Types_holds kU45Out_holds kU45TorusFix_holds kAltTen_holds
      kU45AltFive_holds hH ⟨1, rfl⟩
  have h8106 : R8106At D K P 2 := r8106_at_holds c.std.hSg c.std.h61 hH h8103
  have hzero : pCoreOf 2 D.M ⊓ centralizer (B : Set G) = ⊥ := h8106 B hB
  have hVO : V ≤ pCoreOf 2 D.M :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      hPair.le_M hPair.le_normalizer hPair.elemAbelian.isPGroup
  have hbot : V ⊓ centralizer (B : Set G) = ⊥ := by
    have hle : V ⊓ centralizer (B : Set G) ≤
        pCoreOf 2 D.M ⊓ centralizer (B : Set G) :=
      inf_le_inf_right (centralizer (B : Set G)) hVO
    rw [hzero] at hle
    exact le_bot_iff.mp hle
  exact hfixV hbot

theorem s168e3_false_of_omegaMinus_six_four_natural_original_denominator
    {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV)
    (hs : s15 D.M V₀ V hV L = 1)
    (hN : NatOmegaMinus (lBar V₀ V hV L) (wTil V₀ V hV L)
      (wTil V₀ V hV L ⊓ fixV (lBar V₀ V hV L)) 6 2) : False := by
  obtain ⟨-, K, hF, hFin, b, d, hK, hirr, hR⟩ := hN
  letI := hF
  letI := hFin
  have hchar : CharP K 2 := s16k_charP_two_of_card (a := 2) (by norm_num) hK
  letI := hchar
  have hwt : wTil V₀ V hV L = ⊤ := wTil_eq_top_of_case163_2 c.conc hs
  have hcomm : commV (lBar V₀ V hV L) = ⊤ := by
    rw [commV_eq_commSub]
    simpa [wTil, lBar] using hwt
  have hR' : (FFModel.nat (StatedOmega (StatedQuadMinus 3 K b d))).Realizes
      (lBar V₀ V hV L) ⊤ (fixV (lBar V₀ V hV L)) := by
    have h := hR
    rw [hwt, top_inf_eq] at h
    exact h
  have hF4 : 2 < Nat.card K := by rw [hK]; norm_num
  have hZbot : fixV (lBar V₀ V hV L) = ⊥ :=
    s16_omega_minus_six_cover (K := K) (b := b) (d := d)
      hF4 hirr le_rfl hcomm hR'
  have hN' : NatOmegaMinus (lBar V₀ V hV L) (wTil V₀ V hV L) ⊥ 6 2 :=
    ⟨⟨3, rfl⟩, K, hF, hFin, b, d, hK, hirr, by
      have h : (FFModel.nat (StatedOmega (StatedQuadMinus 3 K b d))).Realizes
          (lBar V₀ V hV L) ⊤ ⊥ := by
        have h := hR
        rw [hwt, top_inf_eq, hZbot] at h
        exact h
      simpa [hwt] using h⟩
  exact s168e3_false_of_omegaMinus_six_four_natural c hs hN'

end

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
