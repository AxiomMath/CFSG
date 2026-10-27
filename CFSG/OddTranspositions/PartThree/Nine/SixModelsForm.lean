module

public import CFSG.OddTranspositions.PartThree.Nine.SixAEight
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.GH73.Reduction
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSp4CentNine
public import CFSG.Certificates.CosetTableShort
public import CFSG.ClassicalInvolution.AschTight.S19FChartD4
public import CFSG.ClassicalInvolution.ModelFacts.G2D4G2Edge
public import CFSG.GH74.GLS.IVK.L2.Torus
public import CFSG.GH74.GLS.IVK.L2.TorusGeneral
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.Der61a
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.Der69
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.Prop67
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.Statements
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.Stmt7
public import CFSG.GH74.GLS.Stage2.Final.Named
public import CFSG.GH74.GLS.Stage2.Local.Statements
public import CFSG.GH74.GLS.Stage4.RestP93
public import CFSG.GH74.GLS.Stage4.RestSetup
public import CFSG.GH74.Generic.Shapes
public import CFSG.GH74.KGroups.L34
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSAContainedSource
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSCSemidihedralKernel
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedLayerOddCoreUnbalancingTriple
public import CFSG.LocalAnalysis.SectionRank.Ccomm.Supercritical
public import CFSG.LocalAnalysis.SectionRank.ThreeInvolutions
public import CFSG.Quasithin.Background.Basic
public import CFSG.RankThree.GroupTheory.SteinbergBYSectionNineResidual
public import CFSG.RankThree.LocalRank.SelectorCases
public import CFSG.RankThree.PartOne.Assembly
public import CFSG.Sporadic.Bridge.LyData
public import CFSG.Sporadic.Bridge.TableSurj
public import CFSG.Sporadic.HN.LevelChainSpec
public import CFSG.Sporadic.Ly.ActionBase
public import CFSG.Sporadic.Ly.CertificateBase
public import CFSG.Sporadic.Ly.FaithSpec
public import CFSG.Sporadic.Ly.OrbitSpec
public import CFSG.Sporadic.Ly.Simple
public import CFSG.Sporadic.LyBase
public import CFSG.Sporadic.McL
public import CFSG.Sporadic.Presentation.Common
public import CFSG.Sporadic.Presentation.Ly
public import CFSG.Sporadic.Schreier.LyChain11
public import Certificates.Certificate3085Base

public section

namespace CFSG.OddTranspositions.PartThree.Nine

open CFSG.Timmesfeld CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72 CFSG.BenderSuzuki

variable {G : Type} [Group G] [Finite G] {D : Set G}

namespace NineSixSetting

variable {hC : HypothesisC D} {T : Sylow 2 (Halpha D hC.alpha)} {S : Sylow 2 G}
  {U : Subgroup G}


theorem false_of_modelsForm (hM : CFSG.GH74.ModelsFormStatement) (h : NineSixSetting hC T S U) :
    False := by
  obtain ⟨S₈, hS₈⟩ := h.sylow_type
  let D₈ : CFSG.EvenSporadicStandard.HNRecog.GH73.A8SylowData ↥(commutator G) :=
    CFSG.EvenSporadicStandard.HNRecog.GH73.A8SylowData.of_sylow S₈ hS₈
  have hnonab : ∃ a b : ↥(commutator G), a * b ≠ b * a := by
    have hLK := pResidualOf_le_commutator h.hyp h.three h.delta h.five.1
    obtain ⟨eL⟩ := nonempty_pResidualOf_mulEquiv h.three h.delta h.five.1
    have hLB : IsBenderGroup (CFSG.Quasithin.pResidualOf 2 (Halpha D hC.alpha)) :=
      isBenderGroup_of_mulEquiv eL h.hyp.bender
    obtain ⟨a, b, hab⟩ := IsBenderGroup.exists_not_commute hLB
    refine ⟨⟨a, hLK a.2⟩, ⟨b, hLK b.2⟩, fun hab' => hab ?_⟩
    exact Subtype.ext (congrArg (fun x : ↥(commutator G) => (x : G)) hab')
  haveI : IsSimpleGroup ↥(commutator G) := h.simple
  have h3 : 3 ≤ CFSG.Open.twoRank ↥(commutator G) :=
    CFSG.EvenSporadicStandard.HNRecog.GH73.three_le_twoRank_of_e16 D₈.exists_e16
  have hX : CFSG.GH74.GH74Conclusion ↥(commutator G) := hM _ hnonab h3 D₈.gen_four
  obtain ⟨P, t, htP, htc, ht2, ht9⟩ := h.exists_central_not_nine_dvd_card_centralizer
  rcases CFSG.EvenSporadicStandard.HNRecog.GH73.survivors D₈ hX with
    h8 | h9 | ⟨p, f, hp, hp2, hf, hq, hL⟩
  · exact h.not_nonempty_mulEquiv_alt8 h8
  · exact h.not_nonempty_mulEquiv_alt9 h9
  · exact ht9 (CFSG.ComponentClassification.CatFactsSp4.nine_dvd_card_centralizer_of_psp4
      hL hp2 P (D₈.card_sylow P) (D₈.card_center P) htP htc ht2)

end NineSixSetting

end CFSG.OddTranspositions.PartThree.Nine
