module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KAdj.StatementB
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23d.Defs
public import CFSG.Quasithin.Background.B4Models
public import CFSG.Quasithin.H13.U4ParPoint
public import CFSG.Open.StatedDefs
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KAdj.LineTransport
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KAdj.Adjust
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KAdj.SU4
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KAdj.SU4Parabolic
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23d.UnitaryTransport
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KGen.SUFixedLine
import CFSG.ClassicalGroups.UnitaryFlag.OrderSylow
import CFSG.ClassicalGroups.UnitaryFlag.StatedBridge
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
import CFSG.ClassicalGroups.UnitaryFlag.PointSylow
import CFSG.LocalAnalysis.SteinbergSFSingleCommModel3UnitaryGen

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.KAdjE

open CFSG.Open CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial CFSG.Quasithin.H13.U4Par
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (flagStabilizer)

theorem su4_exists_mulEquiv_pointStab {W : Type} [CommGroup W] [Finite W]
    {H : Subgroup (MulAut W)} {a : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 a K)
    (hreal : (FFModel.nat (StatedSU 4 (2 ^ a) K)).Realizes H ⊤ ⊥) (S : Sylow 2 ↥H) :
    ∃ φ : ↥(hypSU h 2 0) ≃* ↥H,
      (hypUnitriangular h 2 0).map φ.toMonoidHom = (S : Subgroup ↥H) ∧
        KTabD.pointStab H S = (parP h).map φ.toMonoidHom := by
  haveI := h.finite
  haveI : CharP K 2 := h.charP
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨R, hR, he⟩ := KTabD.exists_isHypTransport_four h
  have hline := KGenProof.sylowFixedLine_statedSU_four (K := K) (r := 2 ^ a)
    (by rw [h.card, ← pow_mul, mul_comm])
  obtain ⟨U₀, hU₀⟩ := su4_exists_sylow_hypUnitriangular h
  let U' : Sylow 2 ↥(StatedSU 4 (2 ^ a) K) :=
    U₀.mapSurjective (f := (hypTransport h hR).toMonoidHom) (hypTransport h hR).surjective
  have hQ := KTabD.map_parP_hypTransport_eq_lineStab h hR he
  have hU' : (U' : Subgroup ↥(StatedSU 4 (2 ^ a) K)) ≤
      KTabD.lineStab (StatedSU 4 (2 ^ a) K) (Pi.single 0 1 + Pi.single 1 1) := by
    rw [← hQ]
    exact Subgroup.map_mono (hU₀ ▸ su4_hypUnitriangular_le_parP h)
  obtain ⟨φ', hφ'U, hφ'Q⟩ := exists_mulEquiv_pointStab_eq_map_sylow hreal hline U' hU' S
  refine ⟨(hypTransport h hR).trans φ', ?_, ?_⟩
  · calc (hypUnitriangular h 2 0).map ((hypTransport h hR).trans φ').toMonoidHom
        = ((U₀ : Subgroup ↥(hypSU h 2 0)).map (hypTransport h hR).toMonoidHom).map
            φ'.toMonoidHom := by
          rw [Subgroup.map_map, hU₀]; rfl
      _ = S := hφ'U
  · rw [hφ'Q, ← hQ, Subgroup.map_map]; rfl

theorem kAdjAt_of_realizes_su4 {W : Type} [CommGroup W] [Finite W] (H : Subgroup (MulAut W))
    {a : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 a K) (ha : 2 ≤ a)
    (hreal : (FFModel.nat (StatedSU 4 (2 ^ a) K)).Realizes H ⊤ ⊥) : KAdjAt W H (2 * a) := by
  haveI := h.finite
  have hcard : Nat.card K = (2 ^ a) ^ 2 := by rw [h.card, ← pow_mul, mul_comm]
  have hSU : IsSUn ↥H 4 a := by
    obtain ⟨π, -, -⟩ := KTabC.exists_natEquiv hreal
    exact ⟨K, inferInstance, h.finite, hcard, ⟨π.symm⟩⟩
  have hNat : NatSUn H ⊤ ⊥ 4 a := ⟨K, inferInstance, h.finite, hcard, hreal⟩
  exact kAdjAt_of_model H (2 * a) a (Or.inr (Or.inr ⟨rfl, hSU, hNat⟩)) (hypUnitriangular h 2 0)
    (flagStabilizer h 2 0 {2}) (parP h) (su4_exists_mulEquiv_pointStab h hreal)
    (su4_isParabolicTwo_flagStabilizer_two h) (su4_hypUnitriangular_le_flagStabilizer_two h)
    (su4_not_flagStabilizer_two_le_parP h)
    (fun P hP hU hnot => su4_flagStabilizer_two_le_of_parabolic h hP hU hnot)
    (fun r _ _ hrc t ht hord =>
      kAdj_model_su4_hyp h ha (su4_dvd_two_pow_sub_one rfl (by omega) hrc) ht hord)

theorem kAdjAt_su4 {W : Type} [CommGroup W] [Finite W] (H : Subgroup (MulAut W)) {n : ℕ}
    (h : ∃ a : ℕ, n = 2 * a ∧ IsSUn ↥H 4 a ∧ NatSUn H ⊤ ⊥ 4 a) (hn : 3 ≤ n) :
    KAdjAt W H n := by
  obtain ⟨a, rfl, -, K, _, _, hK, hreal⟩ := h
  exact kAdjAt_of_realizes_su4 H (unitaryFieldDataOfCard hK) (by omega) hreal

end CFSG.LocalAnalysis.UniquenessCase.UC22.KAdjE
