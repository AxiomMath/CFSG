module

public import CFSG.ClassicalInvolution.Balance.StrongPowSuBlocks

import CFSG.ClassicalGroups.Unitary.Finite
import CFSG.RankThree.PartOne.KF.ClsSUUpper
import CFSG.LinearAlgebra.LinearGroups.UnitaryVectorCount
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.ClassicalInvolution.Balance.PassTwoFinal
public import CFSG.ClassicalInvolution.Models.LinearFrames
public import CFSG.ClassicalInvolution.Models.LinearPairs
public import CFSG.LieType.Ree.SmallReeModelSchreier
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOddLieClassical
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOddLieE6E7Triality
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
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwo
public import CFSG.LocalAnalysis.ComponentInitial.BlockOvergroupDichotomy
public import CFSG.LocalAnalysis.ComponentInitial.GeneralizedFittingProduct
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasFive
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalStandardFormsRegular
public import CFSG.LocalAnalysis.ComponentInitial.SylowPointRecovery
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.ComplementTransfer
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public import TauCeti.LinearAlgebra.Dimension.IsQuadraticExtension
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup.LowRank
import CFSG.Assembly.QuasithinDefs
import CFSG.Quasithin.Background.Basic
import CFSG.RankThree.GroupTheory.SteinbergBYSectionNineResidual
import CFSG.RankThree.LocalRank.SelectorCases
import CFSG.RankThree.PartOne.Assembly
import CFSG.RankThree.PartOne.S10.ThetaContract
import CFSG.RankThree.PartOne.S12.InputsBase
import CFSG.RankThree.PartTwo.Census.Classical.EvenUnitary

public section

namespace CFSG.StandardType.QTwo

open CFSG.ClassicalInvolution.Phan

variable {K : Type} [Field K] [Finite K] [CharP K 2]

private theorem qTwoORD_su_eq_statedSU (hF : Nat.card K = (2 ^ 1) ^ 2) (n : ℕ) :
    Su K 2 1 n = ↥(CFSG.Open.StatedSU n (2 ^ 1) K) := by
  dsimp only [Su]
  rw [CFSG.LieType.Universal.Unitary.SUid_eq_statedSU (F := K) (p := 2) (f := 1) hF n]

theorem card_Su_four (hK : Nat.card K = 4) : Nat.card (Su K 2 1 4) = 25920 := by
  have hF : Nat.card K = (2 ^ 1) ^ 2 := by rw [hK]; norm_num
  have hdata := CFSG.RankThree.PartOne.KFU.unitaryFieldData_two (K := K) (f := 1) hF (by norm_num)
  rw [qTwoORD_su_eq_statedSU (K := K) hF 4]
  have hval : (Nat.card ↥(CFSG.Open.StatedSU 4 (2 ^ 1) K) : ℤ) = 25920 := by
    rw [CFSG.RankThree.PartOne.KFU.card_statedSU_eq (K := K) (f := 1) hdata (n := 4) (by norm_num)]
    decide
  exact_mod_cast hval

theorem card_Su_five (hK : Nat.card K = 4) : Nat.card (Su K 2 1 5) = 13685760 := by
  have hF : Nat.card K = (2 ^ 1) ^ 2 := by rw [hK]; norm_num
  have hdata := CFSG.RankThree.PartOne.KFU.unitaryFieldData_two (K := K) (f := 1) hF (by norm_num)
  rw [qTwoORD_su_eq_statedSU (K := K) hF 5]
  have hval : (Nat.card ↥(CFSG.Open.StatedSU 5 (2 ^ 1) K) : ℤ) = 13685760 := by
    rw [CFSG.RankThree.PartOne.KFU.card_statedSU_eq (K := K) (f := 1) hdata (n := 5) (by norm_num)]
    decide
  exact_mod_cast hval

theorem card_Su_six (hK : Nat.card K = 4) : Nat.card (Su K 2 1 6) = 27590492160 := by
  have hF : Nat.card K = (2 ^ 1) ^ 2 := by rw [hK]; norm_num
  have hdata := CFSG.RankThree.PartOne.KFU.unitaryFieldData_two (K := K) (f := 1) hF (by norm_num)
  rw [qTwoORD_su_eq_statedSU (K := K) hF 6]
  have hval : (Nat.card ↥(CFSG.Open.StatedSU 6 (2 ^ 1) K) : ℤ) = 27590492160 := by
    rw [CFSG.RankThree.PartOne.KFU.card_statedSU_eq (K := K) (f := 1) hdata (n := 6) (by norm_num)]
    decide
  exact_mod_cast hval

theorem isPerfect_Su (hK : Nat.card K = 4) {n : ℕ} (hn : 4 ≤ n) : Group.IsPerfect (Su K 2 1 n) := by
  have hF : Nat.card K = (2 ^ 1) ^ 2 := by rw [hK]; norm_num
  exact CFSG.ClassicalGroups.Unitary.isPerfect_SUid
    (CFSG.ClassicalGroups.Unitary.isUnitaryInvolution_unitaryInvolution (K := K) (p := 2) (f := 1) hF)
    (by omega)
    (fun h3 => absurd h3 (by omega))

end CFSG.StandardType.QTwo

end
