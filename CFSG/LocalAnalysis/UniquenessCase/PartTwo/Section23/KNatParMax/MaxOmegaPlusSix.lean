module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23d.Defs
public import CFSG.Open.StatedDefs

import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KAdj.OmegaPlusModel
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23bOmega6Plus
import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockOrthPlusBlocks
import CFSG.ClassicalGroups.Orthogonal.StatedOmegaElementary
import CFSG.Blueprint.LieModelAPI
import CFSG.CGT.Timmesfeld75.L2Pair
import CFSG.CGT.Timmesfeld75.ListWCBasic
import CFSG.CharacterTheory.CyclicBlocks.Family
import CFSG.CharacterTheory.Semidihedral.Principal.LargePrimeTorusSylowCentralizers
import CFSG.CharacterTheory.Semidihedral.Principal.PrimeTorusBlockAlignment
import CFSG.CharacterTheory.Wreathed.FourPointInvolutionHexagon
import CFSG.CharacterTheory.Wreathed.OrderThirtyTwoWreathFusion
import CFSG.ClassicalGroups
import CFSG.ClassicalInvolution.Models.SymplecticPairs.ShortRoot
import CFSG.Combinatorics.AperiodicCentralInvolution
import CFSG.Combinatorics.AperiodicFiveOfSix
import CFSG.Combinatorics.AperiodicOppositeComponents
import CFSG.Combinatorics.AperiodicSixteenGraphDistances
import CFSG.Combinatorics.OuterLayerPredecessors
import CFSG.GH74.BNPair.Defs
import CFSG.GH74.GLS.Defs
import CFSG.GH74.GLS.IVK.L2.F1
import CFSG.GH74.GLS.Stage2.Local.Statements
import CFSG.GH74.GLS.Stage2.Signalizer.Odd87Defs
import CFSG.GH74.GLS.Stage2.Signalizer.Odd87GrpSubAbs
import CFSG.GH74.KGroups.L3EpsNoNormalThree
import CFSG.GH74.KGroups.L3EpsOutExp
import CFSG.GH74.KGroups.L3EpsOuterLin
import CFSG.LieType.SeitzGeneration.NonabHeisThreeCore
import CFSG.LieType.SeitzGeneration.NonabHeisThreeUnitary
import CFSG.LieType.SeitzGeneration.UnitaryBlocks
import CFSG.LieType.SeitzGeneration.UnitaryHyperScope
import CFSG.LieType.SteinbergBRSemidirectSL2
import CFSG.LinearAlgebra.LinearGroups.UnitaryThreeOverNine
import CFSG.LinearAlgebra.LinearGroups.UnitaryThreeOverNineInvolutions
import CFSG.LinearAlgebra.RootGroupSL.SLFacts
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixStructure
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenCanonicalField
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpExclusion
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpSuzukiCentralizer
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpWedge
import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Reduce
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6Containment
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7bPairs
import CFSG.LocalAnalysis.SectionRank.QTK.CentreFact.Bounded
import CFSG.LocalAnalysis.SectionRank.QTK.EvenOrth
import CFSG.LocalAnalysis.SectionRank.QTK.Exc
import CFSG.LocalAnalysis.SectionRank.QTK.OddOrth
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23bL2Transport
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.StatementsFiveK
import CFSG.LocalAnalysis.UniquenessCase.UC22S20b
import CFSG.Mathlib.LinearAlgebra.BilinForm.Determinant
import CFSG.Models.Transport
import CFSG.Permutation.UnitaryThreeRecognition.Model
import CFSG.Quasithin.Background.A3Structure312
import CFSG.Quasithin.Background.B1More13A
import CFSG.Quasithin.Background.B1More13Defs
import CFSG.Quasithin.Background.B1MoreEleven
import CFSG.Quasithin.Background.B5CompA
import CFSG.Quasithin.Background.B5CompB
import CFSG.Quasithin.Background.B6
import CFSG.Quasithin.Background.B6Example
import CFSG.Quasithin.Background.E2Hyp
import CFSG.Quasithin.Background.E2SolvTwo
import CFSG.Quasithin.Background.F2Equiv
import CFSG.Quasithin.Background.F9FiveStruct
import CFSG.Quasithin.Background.F9G2
import CFSG.Quasithin.Background.F9Geometry
import CFSG.Quasithin.Background.HFixSylBase
import CFSG.Quasithin.Background.HModelTransp
import CFSG.Quasithin.EmptyFaithful.GoldschmidtF112ListC
import CFSG.Quasithin.EmptyFaithful.S142Statements
import CFSG.Quasithin.H13.A5S1326
import CFSG.Quasithin.H13.A5Top
import CFSG.RankThree.CentralLiftSO.SplitTorusWeyl
import CFSG.RankThree.OddKernel.CompleteRankComparison
import CFSG.RankThree.PartOne.KF.ClsPSL
import CFSG.RankThree.PartOne.KF.SU5Model
import CFSG.RankThree.PartOne.KF.SymCtxMatrix
import CFSG.RankThree.PartOne.KF.ToralQuot
import CFSG.RankThree.PartOne.KF.UnitaryModel
import CFSG.RankThree.PartOne.S11c.Sec66PSL
import CFSG.RankThree.PartOne.S11c.Sec66Sp
import CFSG.RankThree.PartOne.S11c.SuFiveD
import CFSG.RankThree.PartOne.S11d.OutSymplectic
import CFSG.RankThree.PartOne.S11d.OutUnitary
import CFSG.RankThree.PartOne.S9.Sylow.ExclusionBasic
import CFSG.Sporadic.Recognition.JankoWongPSLNine
import CFSG.Sporadic.Schreier.J4SProfileNode
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2NormalizedRootSylowCount

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.NatParMax

open CFSG.Open
open CFSG.AGLEmbedding.LeviBlock
open CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit
open CFSG.ClassicalGroups.Orthogonal

private lemma plusFlagStab_one_eq_inf_M04 (K : Type) [Field K] :
    plusFlagStab K 3 ({1} : Finset ℕ) = splitE K ⊓ pointStab K := by
  ext g
  rw [mem_plusFlagStab, Subgroup.mem_inf, mem_pointStab]
  constructor
  · rintro ⟨hgE, hg⟩
    exact ⟨hgE, hg 1 (Finset.mem_singleton.mpr rfl)⟩
  · rintro ⟨hgE, hg⟩
    exact ⟨hgE, fun d hd => by rw [Finset.mem_singleton.mp hd]; exact hg⟩

private lemma map_omegaPlusQZero_eq_inf_M04 (K : Type) [Field K] :
    (KAdjE.omegaPlusQZero K).map (KAdjE.omegaPlusEmb K) = splitE K ⊓ pointStab K := by
  rw [KAdjE.map_omegaPlusQZero K]
  exact plusFlagStab_one_eq_inf_M04 K

private lemma map_top_omegaPlusEmb_M04 (K : Type) [Field K] :
    (⊤ : Subgroup ↥(StatedOmega (StatedQuadPlus 3 K))).map (KAdjE.omegaPlusEmb K) =
      splitE K := by
  have hψ : (statedOmegaPlusEquiv (K := K) (le_rfl : (3 : ℕ) ≤ 3)).toMonoidHom.range = ⊤ :=
    MonoidHom.range_eq_top_of_surjective _
      (statedOmegaPlusEquiv (K := K) (le_rfl : (3 : ℕ) ≤ 3)).surjective
  rw [KAdjE.omegaPlusEmb, Subgroup.map_top, MonoidHom.range_comp, hψ,
    Subgroup.map_top, Subgroup.range_subtype]
  rfl

theorem lineStab_maximal_statedOmegaPlusSix {K : Type} [Field K] [Finite K] [CharP K 2] :
    ∀ Y : Subgroup ↥(StatedOmega (StatedQuadPlus 3 K)),
      KTabD.lineStab (StatedOmega (StatedQuadPlus 3 K)) (Pi.single (Sum.inl 0) 1) ≤ Y →
        Y = KTabD.lineStab (StatedOmega (StatedQuadPlus 3 K)) (Pi.single (Sum.inl 0) 1) ∨
          Y = ⊤ := by
  intro Y hY
  have hQeq : KTabD.lineStab (StatedOmega (StatedQuadPlus 3 K)) (Pi.single (Sum.inl 0) 1)
      = KAdjE.omegaPlusQZero K := rfl
  have hP : (KAdjE.omegaPlusQZero K).map (KAdjE.omegaPlusEmb K) = splitE K ⊓ pointStab K :=
    map_omegaPlusQZero_eq_inf_M04 K
  have hMle : Y.map (KAdjE.omegaPlusEmb K) ≤ splitE K := by
    rw [← map_top_omegaPlusEmb_M04 K]
    exact Subgroup.map_mono le_top
  have hle : splitE K ⊓ pointStab K ≤ Y.map (KAdjE.omegaPlusEmb K) := by
    rw [← hP, ← hQeq]
    exact Subgroup.map_mono hY
  have hBM : borel 3 K ≤ Y.map (KAdjE.omegaPlusEmb K) :=
    borel_le_maxParab_point.trans hle
  by_cases hMP : Y.map (KAdjE.omegaPlusEmb K) = splitE K ⊓ pointStab K
  · left
    apply Subgroup.map_injective (KAdjE.omegaPlusEmb_injective K)
    rw [hQeq, hMP, hP]
  · right
    have htop : Y.map (KAdjE.omegaPlusEmb K) = splitE K :=
      maxParab_point_max hMle hBM hle hMP
    apply Subgroup.map_injective (KAdjE.omegaPlusEmb_injective K)
    rw [htop, map_top_omegaPlusEmb_M04 K]

end CFSG.LocalAnalysis.UniquenessCase.UC22.NatParMax
