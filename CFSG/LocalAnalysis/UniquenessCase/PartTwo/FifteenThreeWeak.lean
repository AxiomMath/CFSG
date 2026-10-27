module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenThreeShape
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenThreeB2t
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenThreeA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenThreeC2
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenThreeD
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenThreeG
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenThreeI
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenThreeZ3
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs16a
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenT7Proof
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight102Basic
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenThreeB2s
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenThreeSemiBotMain
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
public import CFSG.LocalAnalysis.StronglyEmbedded.PSubgroups
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenThreeD1
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs12b
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846d
public import CFSG.LocalAnalysis.UniquenessCase.UCR638
public import CFSG.RankThree.Chevalley.SteinbergCEF4EvenQPlusWeyl
public import CFSG.RankThree.Chevalley.SteinbergCFEvenF4PointwiseInner
public import CFSG.RankThree.Classical.SteinbergBJSymplecticSquareZeroCentralizer
public import CFSG.RankThree.PartTwo.Census.Classical.EvenUnitary

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

@[expose] def Desc153Weak (D : Data G) (V₀ V : Subgroup G) (hV : IsElemAbelian 2 V)
    (L : Subgroup G) : Prop :=
  s15 D.M V₀ V hV L = 1 ∨ Case153_2 D V₀ V hV L ∨ Case153_3 D V₀ V hV L

@[expose] def R15_3Weak (D : Data G) : Prop :=
  ∀ (V₀ V L : Subgroup G) (h : Hyp151 D V₀ V L),
    (∃ φ ∈ Mbar D.M (v1Sub D.M V₀ V h.isElemAbelian L) V h.isElemAbelian,
        InducesTransvection φ (wStar D.M V₀ V h.isElemAbelian L)) →
      Desc153Weak D V₀ V h.isElemAbelian L

theorem s15ThreeRankLeThreeGap_of_evenRank (D : Data G) (he : evenRank G = 3) :
    S15ThreeRankLeThreeGap D := by
  intro hx h614 h76 h82 V₀ V L K₀ h hV hshape hperf hL2 hrs hsig hSg h3 hns q hq h4
  obtain ⟨hqp, hq2⟩ := D.sig_prime q hq
  have hle :=
    CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.pRank_le_three_of_evenRank D he hqp hq2
  omega

theorem fifteen_three_weak (D : Data G) (hx : DataExt D)
    (hMcL : RMcLaughlin) (hDer : RJPrime153) (hNorm : RNormNat153)
    (hT : RTable137) (hRk : RRank3List153) (hAbs : RAbsIrr153) (hSimple : RSimple153)
    (h61 : UC6.R6_1 D) (h63 : UC6.R6_3 D) (h614 : UC6.R6_14 D) (h76 : F07.R76Sig D)
    (h77 : F07.R77E2 D) (hS2 : RSchur2_153) (h127 : R127 D) (h115 : F11.R115 D)
    (h119 : F11.R119 D) (h1217 : R1217 D) (h1214 : F12.R1214 D) (h82 : F08.R82 D)
    (h880 : F08.R880 D) (h1111 : R1111_153 D) (hAut : RAutRank153) (hCov : RCover3Rank153)
    (hSchur : RSchur153) (hIso : RIso153) (hNotJ2 : RNotJ2) (hPerfT : RPerfType153)
    (hTen : RTenP153 D) (hsig : D.sig ⊆ D.sig1) (hSg : UC6S846.SigmaStd D)
    (hgapSig : S15ThreeSigSubPiGap D) (hgapRank : S15ThreeRankLeThreeGap D) :
    R15_3Weak D := by
  intro V₀ V L h htr
  have hne : D.sig.Nonempty := hx.sig_nonempty
  have hV : IsElemAbelian 2 V := h.isElemAbelian
  have hL : barSub V₀ V hV L ≠ ⊥ := by
    obtain ⟨φ, -, hφ⟩ := htr
    exact s15_Three_barSub_ne_bot h hφ
  have hsemi := s15_Three_semisimple_AW_of_sSup_irr h (s15_semiBot_sSup_irr_star h1217 h hL htr)
  obtain ⟨K₀, hshape⟩ := s15_Three_shape hMcL hDer hNorm h1217 h hL hsemi
    (fun I I' hI hI' => s15_Three_trans_AW hx h61 h127 h1214 h1217 h hL hsemi I I' hI hI') htr
  by_cases hZ : IsCyclicOrd ↥(barSub V₀ V hV K₀) 3
  · have hZ3 := hshape.2.2.2.1.resolve_left (fun hp => by
      have : IsMulCommutative ↥(barSub V₀ V hV K₀) := hZ.1.isMulCommutative
      have : Subsingleton (↥(barSub V₀ V hV K₀) ⧸ Subgroup.center _) :=
        QuotientGroup.subsingleton_iff.2 Subgroup.center_eq_top
      exact not_nontrivial _ (hSimple _ _ _ _ hp).1.2.toNontrivial)
    exact Or.inr (Or.inr (s15_Three_case_three h127 h1217 hTen h hV hL hshape hZ3))
  · have hperf := hshape.2.2.2.1.resolve_right (fun hz => hZ hz.1)
    by_cases hexc : s15Rs D V₀ V hV L K₀ = 1 ∧ s15ExcList ↥(lBar V₀ V hV L)
    · by_cases hL2 : s15ListTwo ↥(lBar V₀ V hV L)
      · exact Or.inr (Or.inl (s15_Three_case_two_small h61 h63 h127 h115 h1111 h1217 hAut hAbs hT
          hPerfT hne h hV hL hshape hexc.1 hperf hL2))
      · exact Or.inl ((s15_Three_rs_eq_one_iff D V₀ V hV L K₀).1 hexc.1).2
    · have hO1 : s15O1a D V := by
        rcases s15_Three_trich hT hRk hAbs hSimple h127 h119 h1217 h hV hL hshape with
          hO | hz | hb
        · exact hO
        · exact absurd hz hZ
        · exact absurd hb hexc
      exact Or.inr (Or.inl (s15_Three_case_two_big hgapSig hgapRank hx h61 h63 h614 h76 h77
        hSimple hS2 h127 h119 h1217 h82 h880 h1111 hRk hCov hSchur hIso hNotJ2 hPerfT hsig hSg hne
        h hV hshape hperf hO1 hexc))

theorem s15_T7_rt7One_of_fifteen_three_weak (D : Data G) (h153 : R15_3Weak D)
    (h129 : R129_1 D) (h1217 : R1217 D) : RT7One D := by
  intro V₀ V L h hL F C K hcfg
  have hQ := s15_T7_exists_group D h.hyp151 hcfg
  have hdesc := h153 V₀ V L h.hyp151 (s15_T7_exists_transvection D h.hyp151 hQ)
  have hs := fifteen_five D h129 h1217 h h.hyp151.isElemAbelian hL
  rcases hdesc with h1 | h2 | h3
  · omega
  · exact s15_T7_case2 D h.hyp151 hs hQ h2
  · exact (s15_T7_case3 D h.hyp151 hQ h3).elim

theorem rt7_of_fifteen_three_weak (D : Data G) (h153 : R15_3Weak D) (h129 : R129_1 D)
    (h1217 : R1217 D) : RT7 D :=
  s15_T7_rt7_of_one D (s15_T7_rt7One_of_fifteen_three_weak D h153 h129 h1217)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
