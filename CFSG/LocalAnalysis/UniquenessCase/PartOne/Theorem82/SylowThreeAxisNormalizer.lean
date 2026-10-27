module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.PerfectCentralizerNormalizer
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CaseTwoSylow
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSmallCoverCentralizer
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Conclusion76Three
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Basic
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846e
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Fourteen1
import CFSG.LocalAnalysis.UniquenessCase.UC22P22e
import CFSG.LocalAnalysis.UniquenessCase.UC22P22n
import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.Blueprint.LieModelAPI
public import CFSG.GroupTheory.CoprimeActionSupport.AbelianEquivalence
public import CFSG.GroupTheory.CoprimeActionSupport.Geometry
public import CFSG.LocalAnalysis.RankThreeUC.Notation
public import CFSG.LocalAnalysis.RankThreeUC.Section3.CoprimeSpecialGroups.CommPowPow
public import CFSG.LocalAnalysis.RankThreeUC.Section5.ExtraspecialOrder
public import CFSG.LocalAnalysis.RankThreeUC.SourceSetting.AschbacherCommon
public import CFSG.LocalAnalysis.RankThreeUC.WeakModules
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846d
public import CFSG.LocalAnalysis.UniquenessCase.UCR638
public import CFSG.RankThree.OddKernel.CentralCoverComponentModels
public import CFSG.RankThree.PartTwo.Sec12.Item128Bar
public import Certificates.Certificate8052
public import Certificates.Kernel.Sporadic.Fi22.C2068
public import Certificates.Kernel.Sporadic.Fi22.C3151
import CFSG.Adapters.StatedClassicalSmallOrders
import CFSG.ClassicalInvolution.Models.SymplecticPairs.Quadruple
import CFSG.ClassicalInvolution.QuaternionStructure
import CFSG.ClassicalInvolution.WeakCT.Main
import CFSG.GH74.GLS.Defs
import CFSG.GH74.GLS.Stage1.Thm3.Sec5.Closed
import CFSG.GH74.GLS.Stage1.Thm3.Sec5.Statements
import CFSG.GH74.GLS.Stage1.Thm6.Sec12.Defs
import CFSG.GH74.GLS.Stage1.Thm6.Sec12.Ext
import CFSG.GH74.GLS.Stage2.Final.LayerFDerive
import CFSG.LieType.CurtisTits.Adjoint
import CFSG.LieType.Ree.LargeReeEightTorus
import CFSG.LieType.Ree.LargeReeInvolutionTwoCentralizers
import CFSG.LocalAnalysis.ComponentClassification.CatLeafOddB
import CFSG.LocalAnalysis.ComponentClassification.ExcSelectorEvenE6
import CFSG.LocalAnalysis.ComponentClassification.ExcSelectorEvenTriality
import CFSG.LocalAnalysis.ComponentClassification.ExcSelectorOddE6
import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeMax
import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalOddCentralizer
import CFSG.LocalAnalysis.ComponentInitial.GL3TwoFixedModelCases
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyBasic
import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdentLieAlt
import CFSG.LocalAnalysis.SeitzReduction.CrossCharInputs
import CFSG.LocalAnalysis.SeitzReduction.E6PilotHR4
import CFSG.LocalAnalysis.SeitzReduction.E6PilotLeviPerp
import CFSG.LocalAnalysis.SeitzReduction.E8PilotQ2PositionWork
import CFSG.LocalAnalysis.SeitzReduction.E8PilotSwapLift
import CFSG.LocalAnalysis.SeitzReduction.EPilotEndGraphE6
import CFSG.LocalAnalysis.SeitzReduction.EPilotEndGraphTwistedXi
import CFSG.LocalAnalysis.SeitzReduction.F4PilotCatEvenClassical
import CFSG.LocalAnalysis.SeitzReduction.F4PilotCatSporadic
import CFSG.LocalAnalysis.SeitzReduction.F4PilotEndField
import CFSG.LocalAnalysis.SeitzReduction.F4PilotFieldNeighbourFix
import CFSG.LocalAnalysis.SeitzReduction.F4PilotFieldNeighbourLift
import CFSG.LocalAnalysis.SeitzReduction.F4PilotInnerField
import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveWSmall
import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveWSylow
import CFSG.LocalAnalysis.SeitzReduction.LinearPilotSwapFactorNormalGraph
import CFSG.LocalAnalysis.SeitzReduction.LinearPilotTwistedFusion
import CFSG.LocalAnalysis.SeitzReduction.RankOneBranches
import CFSG.LocalAnalysis.SeitzReduction.RankOneCatSL2TwoFixedA5
import CFSG.LocalAnalysis.SeitzReduction.RankOneHypStarDef
import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotAlignImagesSwap
import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotUniqueTypeGraph
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DefsHyp
import CFSG.RankThree.Chevalley.SteinbergCEF4EvenQPlusWeyl
import CFSG.RankThree.Chevalley.SteinbergCFEvenF4PointwiseInner
import CFSG.RankThree.Classical.SteinbergBJSymplecticSquareZeroCentralizer
import CFSG.RankThree.PartTwo.Census.Classical.EvenUnitary

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.SylowThreeData

open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7

variable {G : Type} [Group G] [Finite G]

theorem normalizer_axis_le_of_three_calC
    (hSE : StronglyEmbeddedFive)
    (hSAlt : StronglyEmbeddedSolvableAltTen)
    (hKSM : CFSG.LocalAnalysis.RankThreeUC.S15.KSMAlt)
    (d : SylowThreeData G)
    (k : Sec7Core4 G) (hkM : k.M = d.M)
    (he : CFSG.Open.evenRank G ≤ 3) (h5 : 5 ≤ k.p)
    (hcal : ∀ i, d.Lf i ∈ calC d.M)
    (hinj : Function.Injective d.Lf)
    (hpK : ∀ i, k.p ∣ Nat.card (d.Lf i))
    (hZ : ∀ i, ¬ k.p ∣ Nat.card (Subgroup.center (Bar2 (d.Lf i))))
    (i : Fin 3) :
    Subgroup.normalizer (d.A i : Set G) ≤ d.M := by
  classical
  obtain ⟨b, hbgen⟩ :=
    (Subgroup.isCyclic_iff_exists_zpowers_eq_top (d.A i)).mp (d.isCyclic_A i)
  have hb3 : orderOf b = 3 := by
    rw [← Nat.card_zpowers, hbgen, d.card_A i]
  have hbA : b ∈ d.A i := hbgen ▸ Subgroup.mem_zpowers b
  have hbLf : b ∈ d.Lf i := d.H_le_Lf i (d.A_le_H i hbA)
  have hbr : b ^ 3 = 1 := by simpa [hb3] using pow_orderOf_eq_one b
  have hpair : ∃ j k2 : Fin 3, j ≠ i ∧ k2 ≠ i ∧ j ≠ k2 := by
    fin_cases i
    · exact ⟨1, 2, by decide, by decide, by decide⟩
    · exact ⟨0, 2, by decide, by decide, by decide⟩
    · exact ⟨0, 1, by decide, by decide, by decide⟩
  obtain ⟨j, k2, hji, hk2i, hjk2⟩ := hpair
  have hdij : d.Lf i ≠ d.Lf j := fun h => hji (hinj h.symm)
  have hdik2 : d.Lf i ≠ d.Lf k2 := fun h => hk2i (hinj h.symm)
  have hdjk2 : d.Lf j ≠ d.Lf k2 := fun h => hjk2 (hinj h)
  obtain ⟨X, hXle, hXperf, hXrank⟩ :=
    CFSG.LocalAnalysis.UniquenessCase.PartTwo.s16_exists_perfect_centralizer_of_three_calC
      (hcal i) (hcal j) (hcal k2) hdij hdik2 hdjk2
      k.prime k.odd Nat.prime_three (by norm_num)
      (hpK j) (hpK k2) (hZ j) (hZ k2) hbLf hbr
  have hXM : X ≤ k.M := by
    rw [hkM]
    exact (hXle.trans inf_le_left).trans (sup_le (d.hLM j) (d.hLM k2))
  have hN := Sec7Core4.normalizer_zpowers_le_of_perfect_centralizer hSE hSAlt hKSM k he h5
    hb3 hXM (hXle.trans inf_le_right) hXperf hXrank
  rw [hkM, hbgen] at hN
  exact hN

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.SylowThreeData
