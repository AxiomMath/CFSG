module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.StatementsEightSz
import CFSG.RankThree.PartTwo.KFacts.AutSzTwoPower
import CFSG.LocalAnalysis.EvenBN.GMSK.SzFacts
import CFSG.SignalizerFunctorTheorem.McBride.Models.Suzuki.Local
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
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.StatementsComponents
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.StatementsEightK
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

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.BenderSuzuki.MatrixGroups
open CFSG.BenderSuzuki.PFAppendixIII
open CFSG.ComponentClassification.AschbacherToolkit.Bender.SuzukiAut
open scoped Pointwise

theorem kSzTwoAut_holds : KSzTwoAut := by
  intro X _ _ a hSz S θ hθ hS
  obtain ⟨m, hm, rfl, ⟨e⟩⟩ :=
    CFSG.LocalAnalysis.EvenBN.GMSK.exists_mulEquiv_sz_of_lieModel_twistedB2 hSz
  let e' : X ≃* SuzukiMatrixGroup m :=
    e.trans (CFSG.SignalizerFunctorTheorem.McBride.SzModel.szEquiv m)
  let S' : Sylow 2 (SuzukiMatrixGroup m) :=
    Sylow.mapSurjective (f := e'.toMonoidHom) e'.surjective S
  let θ' : MulAut (SuzukiMatrixGroup m) := MulAut.congr e' θ
  have hS' : (S' : Subgroup (SuzukiMatrixGroup m)) =
      (S : Subgroup X).map e'.toMonoidHom := rfl
  have hθ' : ∃ n : ℕ, orderOf θ' = 2 ^ n := by
    obtain ⟨n, hn⟩ := hθ
    refine ⟨n, ?_⟩
    change orderOf (MulAut.congr e' θ) = 2 ^ n
    rw [MulEquiv.orderOf_eq, hn]
  have hS'norm : ∀ x ∈ (S' : Subgroup (SuzukiMatrixGroup m)),
      θ' x ∈ (S' : Subgroup (SuzukiMatrixGroup m)) := by
    intro x hx
    rw [hS'] at hx ⊢
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    refine Subgroup.mem_map.mpr ⟨θ y, hS y hy, ?_⟩
    simp [θ', MulAut.congr_apply]
  obtain ⟨s', hs', hθ's'⟩ :=
    CFSG.RankThree.PartTwo.KFacts.exists_eq_conj_of_two_pow_sylow m hm S' θ' hθ' hS'norm
  refine ⟨e'.symm s', ?_, ?_⟩
  · rw [hS'] at hs'
    obtain ⟨y, hy, hyeq⟩ := Subgroup.mem_map.mp hs'
    rw [← hyeq]
    change e'.symm (e' y) ∈ (S : Subgroup X)
    rw [MulEquiv.symm_apply_apply]
    exact hy
  · calc θ = (MulAut.congr e').symm θ' := by
          rw [show θ' = MulAut.congr e' θ from rfl]
          exact (MulEquiv.symm_apply_apply _ _).symm
      _ = (MulAut.congr e').symm (MulAut.conj s') := by rw [hθ's']
      _ = MulAut.conj (e'.symm s') := by
          ext x
          simp [MulAut.congr_symm_apply, MulAut.conj_apply, map_mul, map_inv]

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
