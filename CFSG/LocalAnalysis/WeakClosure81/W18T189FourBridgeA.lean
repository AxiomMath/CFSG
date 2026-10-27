module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafInputs
public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagOrder
public import CFSG.Open.StatedDefs
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.CentralResidueMaps
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.NormalizerClassLifting
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.PrincipalClassDefects
public import CFSG.CharacterTheory.Semidihedral.Principal.DegreeZeroGram
public import CFSG.CharacterTheory.TwoRankLowerBound.BrauerCharacterCriterion
public import CFSG.LieType.BorelTits.CompleteFlag
public import CFSG.LieType.Ree.SuzukiSimple
public import CFSG.LieType.Universal.SpinOmega.Range
public import CFSG.LinearAlgebra.LinearGroups.CoordinateData
public import CFSG.LocalAnalysis.ComponentClassification.BlockCentralSylowEquality
public import CFSG.LocalAnalysis.ComponentClassification.BlockFourFactorSupport
public import CFSG.LocalAnalysis.ComponentClassification.BlockLargeProductInvolutions
public import CFSG.LocalAnalysis.ComponentClassification.BlockMovedFactorSylowCentral
public import CFSG.LocalAnalysis.ComponentClassification.BlockNormalizerOrder
public import CFSG.LocalAnalysis.ComponentClassification.BlockPermutationSylowLifting
public import CFSG.LocalAnalysis.ComponentClassification.BlockStrictFullSylowAbelian
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafBasic
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalDescentEndpoint
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFiveStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionModels
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointPlusBorelModel
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareField
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixComponentsCover
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixModelGeometry
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalTraceZeroCoordinates
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBProjectiveInvolutionStructure
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeMax
public import CFSG.LocalAnalysis.ComponentClassification.KProper
public import CFSG.LocalAnalysis.ComponentClassification.LabeledBlockPermutation
public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalOddCentralizer
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrCriticalStandard
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasFive
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalStandardFormsRegular
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldPrimeOrderFixedSubfield
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.OrderThreeNormalizer
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGammaL2PSLRangeCentralizer
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinInvolutionCount
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinRestrictionSixCount
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinUDecomposition
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationEleven
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationTen
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationTenStructuralIdentities
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2FieldProjectionArithmetic
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2OrderPSubgroupCount
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Suzuki.OddGraphReconstruction
public import Certificates.Certificate1
public import Certificates.Certificate10
public import Certificates.Certificate11
public import Certificates.Certificate12
public import Certificates.Certificate2
public import Certificates.Certificate3
public import Certificates.Certificate4
public import Certificates.Certificate42
public import Certificates.Certificate44
public import Certificates.Certificate5
public import Certificates.Certificate6
public import Certificates.Certificate7
public import Certificates.Certificate8
public import Certificates.Certificate9
public import TauCeti.LinearAlgebra.Dimension.IsQuadraticExtension
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.ComponentClassification.CatLeaf
open scoped MatrixGroups

theorem pglb_lieOrderNumerator_psl_two (q : ℕ) :
    lieOrderNumerator .PSL 2 q = q * (q ^ 2 - 1) := by
  simp only [lieOrderNumerator]
  rw [Finset.prod_Icc_succ_top (show 2 ≤ 1 + 1 by norm_num)]
  simp

theorem pglb_lieOrderNumerator_psl_three (q : ℕ) :
    lieOrderNumerator .PSL 3 q = q ^ 3 * (q ^ 2 - 1) * (q ^ 3 - 1) := by
  simp only [lieOrderNumerator]
  rw [Finset.prod_Icc_succ_top (show 2 ≤ 2 + 1 by norm_num)]
  rw [Finset.prod_Icc_succ_top (show 2 ≤ 1 + 1 by norm_num)]
  simp
  ring

theorem pglb_lieOrderNumerator_psu_three (q : ℕ) :
    lieOrderNumerator .PSU 3 q = q ^ 3 * (q ^ 2 - 1) * (q ^ 3 + 1) := by
  simp only [lieOrderNumerator]
  rw [Finset.prod_Icc_succ_top (show 2 ≤ 2 + 1 by norm_num)]
  rw [Finset.prod_Icc_succ_top (show 2 ≤ 1 + 1 by norm_num)]
  norm_num
  ring

theorem pglb_lieOrderDivisor_psl_two (q : ℕ) :
    lieOrderDivisor .PSL 2 q = Nat.gcd 2 (q - 1) := rfl

theorem pglb_lieOrderDivisor_psl_three (q : ℕ) :
    lieOrderDivisor .PSL 3 q = Nat.gcd 3 (q - 1) := rfl

theorem pglb_lieOrderDivisor_psu_three (q : ℕ) :
    lieOrderDivisor .PSU 3 q = Nat.gcd 3 (q + 1) := rfl

theorem pglb_card_gl_two (K : Type) [Field K] [Finite K] :
    Nat.card (GL (Fin 2) K) = (Nat.card K ^ 2 - 1) * (Nat.card K ^ 2 - Nat.card K) := by
  rw [CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_GL_eq (K := K) 2]
  rw [Finset.prod_Icc_succ_top (show 1 ≤ 1 + 1 by norm_num)]
  rw [Finset.prod_Icc_succ_top (show 1 ≤ 1 + 0 by norm_num)]
  simp
  rw [show Nat.card K ^ 2 - Nat.card K = Nat.card K * (Nat.card K - 1) by
    rw [pow_two, Nat.mul_sub_left_distrib, mul_one]]
  ring

theorem pglb_card_statedScalars_two (K : Type) [Field K] [Finite K] :
    Nat.card ↥(CFSG.Assembly.LowTwoRank.StatedScalars (Fin 2) K) = Nat.card K - 1 := by
  have hinj : Function.Injective
      (Matrix.GeneralLinearGroup.scalar (Fin 2) : Kˣ →* GL (Fin 2) K) := by
    intro a b h
    refine Units.ext ((Matrix.scalar_inj (n := Fin 2)).mp ?_)
    exact congrArg (fun g : GL (Fin 2) K => (g : Matrix (Fin 2) (Fin 2) K)) h
  rw [CFSG.Assembly.LowTwoRank.StatedScalars,
    ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, Nat.card_units]

end CFSG.LocalAnalysis.WeakClosure81

end
