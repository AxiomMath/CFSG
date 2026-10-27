module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KAdj.StatementB
public import CFSG.Quasithin.Background.B4Models
public import CFSG.Open.StatedDefs

import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KAdj.Sp
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KAdj.SpParabolic
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KAdj.LineTransport
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KAdj.Adjust
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23d.FixedLineSp
import CFSG.LocalAnalysis.ComponentInitial.SymplecticFlagOrder
import CFSG.LocalAnalysis.UniquenessCase.UC22P22d
public import CFSG.CGT.Timmesfeld75.L2Pair
public import CFSG.CGT.Timmesfeld75.ListWCBasic
public import CFSG.CharacterTheory.CyclicBlocks.Family
public import CFSG.CharacterTheory.Semidihedral.Principal.LargePrimeTorusSylowCentralizers
public import CFSG.CharacterTheory.Semidihedral.Principal.PrimeTorusBlockAlignment
public import CFSG.CharacterTheory.Wreathed.FourPointInvolutionHexagon
public import CFSG.CharacterTheory.Wreathed.OrderThirtyTwoWreathFusion
public import CFSG.ClassicalGroups
public import CFSG.ClassicalInvolution.Models.SymplecticPairs.ShortRoot
public import CFSG.Combinatorics.AperiodicCentralInvolution
public import CFSG.Combinatorics.AperiodicFiveOfSix
public import CFSG.Combinatorics.AperiodicOppositeComponents
public import CFSG.Combinatorics.AperiodicSixteenGraphDistances
public import CFSG.Combinatorics.OuterLayerPredecessors
public import CFSG.GH74.BNPair.Defs
public import CFSG.GH74.GLS.IVK.L2.F1
public import CFSG.GH74.KGroups.L3EpsNoNormalThree
public import CFSG.GH74.KGroups.L3EpsOutExp
public import CFSG.GH74.KGroups.L3EpsOuterLin
public import CFSG.LieType.SeitzGeneration.NonabHeisThreeCore
public import CFSG.LieType.SeitzGeneration.NonabHeisThreeUnitary
public import CFSG.LieType.SeitzGeneration.UnitaryBlocks
public import CFSG.LieType.SeitzGeneration.UnitaryHyperScope
public import CFSG.LinearAlgebra.LinearGroups.UnitaryThreeOverNine
public import CFSG.LinearAlgebra.LinearGroups.UnitaryThreeOverNineInvolutions
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixStructure
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenCanonicalField
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpExclusion
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpSuzukiCentralizer
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpWedge
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7bPairs
public import CFSG.LocalAnalysis.SectionRank.QTK.CentreFact.Bounded
public import CFSG.LocalAnalysis.SectionRank.QTK.EvenOrth
public import CFSG.LocalAnalysis.SectionRank.QTK.Exc
public import CFSG.LocalAnalysis.SectionRank.QTK.OddOrth
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.StatementsRootModule
public import CFSG.LocalAnalysis.UniquenessCase.UC22S20b
public import CFSG.Mathlib.LinearAlgebra.BilinForm.Determinant
public import CFSG.Permutation.UnitaryThreeRecognition.Model
public import CFSG.Quasithin.EmptyFaithful.Setting
public import CFSG.RankThree.CentralLiftSO.SplitTorusWeyl
public import CFSG.RankThree.OddKernel.CompleteRankComparison
public import CFSG.RankThree.PartOne.KF.ClsPSL
public import CFSG.RankThree.PartOne.KF.SU5Model
public import CFSG.RankThree.PartOne.KF.SymCtxMatrix
public import CFSG.RankThree.PartOne.KF.ToralQuot
public import CFSG.RankThree.PartOne.KF.UnitaryModel
public import CFSG.RankThree.PartOne.S11c.Sec66PSL
public import CFSG.RankThree.PartOne.S11c.Sec66Sp
public import CFSG.RankThree.PartOne.S11c.SuFiveD
public import CFSG.RankThree.PartOne.S11d.OutSymplectic
public import CFSG.RankThree.PartOne.S11d.OutUnitary
public import CFSG.RankThree.PartOne.S9.Sylow.ExclusionBasic
public import CFSG.Sporadic.Recognition.JankoWongPSLNine
public import CFSG.Sporadic.Schreier.J4SProfileNode
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2NormalizedRootSylowCount
import CFSG.LocalAnalysis.UniquenessCase.UC22Bridge

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.KAdjE

open CFSG.Open CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.UniquenessCase.UC22

theorem kAdjAt_of_realizes_sp {W : Type} [CommGroup W] [Finite W] (H : Subgroup (MulAut W))
    (m : ℕ) {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ} (hK : Nat.card K = 2 ^ n)
    (hn : 2 ≤ n) (hreal : (FFModel.nat (StatedSp (m + 2) K)).Realizes H ⊤ ⊥) :
    KAdjAt W H n := by
  refine kAdjAt_of_model H n n (Or.inl rfl) (SymplecticFlag.unipotent (m + 2) K)
    (SymplecticHigher.flagStabilizer (m + 2) K (Set.Icc 2 (m + 2)))
    (KTabD.lineStab (StatedSp (m + 2) K) (Pi.single (Sum.inl 0) 1)) ?_
    (isParabolicTwo_flagStabilizer_alpha m K) (unipotent_le_flagStabilizer_alpha m K)
    (not_flagStabilizer_alpha_le_lineStab m K)
    (fun P hP hU hnot => flagStabilizer_alpha_le_of_parabolic m hP hU hnot)
    (fun r hr hr2 _ t ht hord => kAdj_model_sp hK hn m (hr.odd_of_ne_two hr2) ht hord)
  intro S
  obtain ⟨U, hU⟩ := SymplecticFlag.exists_sylow_unipotent (K := K) 2 (m + 2)
  have hUle : (U : Subgroup ↥(StatedSp (m + 2) K)) ≤
      KTabD.lineStab (StatedSp (m + 2) K) (Pi.single (Sum.inl 0) 1) := by
    rw [hU]
    exact unipotent_le_lineStab m K
  obtain ⟨φ, h1, h2⟩ := exists_mulEquiv_pointStab_eq_map_sylow hreal
    (KTabD.sylowFixedLine_statedSp (K := K) (m + 2)) U hUle S
  refine ⟨φ, ?_, h2⟩
  rw [← hU]
  exact h1

theorem kAdjAt_sp4 {W : Type} [CommGroup W] [Finite W] (H : Subgroup (MulAut W)) {n : ℕ}
    (h : IsSp4 ↥H n ∧ NatSpn H ⊤ ⊥ 4 n) (hn : 3 ≤ n) : KAdjAt W H n := by
  obtain ⟨-, -, K, hKf, hKfin, hKcard, hreal⟩ := h
  letI : Field K := hKf
  letI : Finite K := hKfin
  haveI : CharP K 2 := uc22p22d_charP_two (by omega) hKcard
  exact kAdjAt_of_realizes_sp H 0 hKcard (by omega) hreal

theorem kAdjAt_sp6 {W : Type} [CommGroup W] [Finite W] (H : Subgroup (MulAut W)) {n : ℕ}
    (h : IsSpn ↥H 6 n ∧ NatSpn H ⊤ ⊥ 6 n) (hn : 3 ≤ n) : KAdjAt W H n := by
  obtain ⟨-, -, K, hKf, hKfin, hKcard, hreal⟩ := h
  letI : Field K := hKf
  letI : Finite K := hKfin
  haveI : CharP K 2 := uc22p22d_charP_two (by omega) hKcard
  exact kAdjAt_of_realizes_sp H 1 hKcard (by omega) hreal

end CFSG.LocalAnalysis.UniquenessCase.UC22.KAdjE
