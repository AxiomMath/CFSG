module

public import CFSG.RankThree.PartTwo.Sec18.Statements
public import CFSG.RankThree.PartTwo.Sec18.SimsItem186HStatement
import CFSG.RankThree.PartTwo.Sec18.Item188Quot
import CFSG.RankThree.PartTwo.Sec18.Item183OneProofRem
import CFSG.RankThree.PartTwo.Sec18.Item183NMProofCb
import CFSG.RankThree.PartTwo.Sec18.Item189Glue
import CFSG.CharacterTheory.Semidihedral.OddFieldLift
import CFSG.LinearAlgebra.LinearGroups.CoordinateData
import CFSG.LocalAnalysis.AGLEmbedding.D1GlobalU
import CFSG.LocalAnalysis.AGLEmbedding.Extremal
import CFSG.LocalAnalysis.AGLEmbedding.TwoCoreObstruction
import CFSG.LocalAnalysis.AGLEmbedding.WeakBlockInputs
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGraphFieldArithmetic
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGraphFieldUnitaryData
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCorePrimeCore
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHigherLinearFieldDeterminant
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalDescentEndpoint
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFiveStructure
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFixedTransfer
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionModels
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointPlusBorelModel
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareField
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareStructure
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixComponentsCover
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixModelGeometry
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalTraceZeroCoordinates
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBProjectiveInvolutionStructure
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticBField
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticBLinear
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticRepresentationOdd
import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSUFieldOddCore
import CFSG.LocalAnalysis.ComponentClassification.UnbalancingLocalSmallSourceLinear
import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
import CFSG.LocalAnalysis.ComponentInitial.GL3TwoFixedModelSelector
import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasFive
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalStandardFormsRegular
import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerImageCompletion
import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerPreimages
import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerRestrictionCompletion
import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
import CFSG.RankThree.PartTwo.Sec18.Item183OneProofRemHc
import CFSG.RankThree.PartTwo.Sec18.Item183OneProofRemRank
import CFSG.RankThree.PartTwo.Sec19.Item194Used
import CFSG.RankThree.PartTwo.Sec19.Steps195
import CFSG.RankThree.PartTwo.Sec20.Alt20
import CFSG.RankThree.PartTwo.Sec6.Item612
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
import Certificates.Certificate43
import TauCeti.LinearAlgebra.Dimension.IsQuadraticExtension
import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis
import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup.LowRank

public section

namespace CFSG.RankThree.PartTwo.Sec18

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late

theorem item188_of (h1846 : Item184_6) (h186 : Item186H) (h187 : Item187) (hrem : Rem187) :
    Item188 := by
  intro G _ _ A M hstd hcon H hH
  by_contra hne
  obtain ⟨H', c, hsec, h7⟩ := hrem G A M hstd ⟨H, hH.prop, hne⟩
  obtain ⟨-, ⟨hSmax, hNS⟩, -, hmaxN⟩ := h186 G A M H' c hsec h7
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set L := inSubgroup perfectResidual H'
  set S := CFSG.Open.pCoreOf 2 (H' ⊓ M)
  set O := inSubgroup (CFSG.pPrimeCore 3) M with hOdef
  have hAM : A ≤ M := sec18Std_le hstd
  have hWM : Subgroup.normalizer (A : Set G) ≤ M := Rem187QProof.normalizer_le hstd
  obtain ⟨P, hPW⟩ := CFSG.ABGLocalTools.exists_isSylowOf 3 (Subgroup.normalizer (A : Set G))
  have hPT : CFSG.ABGLocalTools.IsSylowOf 3 P ⊤ := h1846 G A M H' c hsec P hPW
  have hPM : P ≤ M := hPW.le.trans hWM
  have hP : CFSG.ABGLocalTools.IsSylowOf 3 P M := hPT.of_le hPM le_top
  have hA3grp : IsPGroup 3 A := (isE27_of_mem_partTwoE hstd.mem_partTwoE).isPGroup
  have hAP : A ≤ P := by
    have hsup : P ⊔ A = P :=
      hPW.eq_of_le le_sup_left (sup_le hPW.le Subgroup.le_normalizer)
        (IsPGroup.to_sup_of_normal_right' hPW.isPGroup hA3grp hPW.le)
    exact le_sup_right.trans hsup.le
  have hA3 : ∀ x : G, x ^ 3 = 1 → (∀ a ∈ A, a * x = x * a) → x ∈ A :=
    fun x hx hxc => Item183NMProof.mem_of_commute_of_sec18Std hstd hx hxc
  have hS2 : IsPGroup 2 S := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (H' ⊓ M)
  have hTM : S ≤ M := (CFSG.LieType.BorelTits.pCoreOf_le 2 (H' ⊓ M)).trans inf_le_right
  have hSmax' : Maximal (· ∈ invariantPiSubgroups ⊤ A (piOf 2)) S := hSmax
  have hAT : A ≤ Subgroup.normalizer (S : Set G) :=
    ((mem_invariantPiSubgroups_piOf_iff Nat.prime_two).mp hSmax'.1).2.2
  have hSO : S ≤ O :=
    CFSG.RankThree.PartTwo.Sec18.Item188Proof.le_inSubgroup_pPrimeCore_of_isPConstrained hcon hP
      hAP hPW.le hA3 hS2 hTM hAT
  have hO3 : ¬ 3 ∣ Nat.card O := by
    rw [hOdef, inSubgroup, Subgroup.card_map_of_injective M.subtype_injective]
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp CFSG.pPrimeCore_coprime_card
  have hMO : M ≤ Subgroup.normalizer (O : Set G) :=
    CFSG.RankThree.PartTwo.Late.le_normalizer_inSubgroup_pPrimeCore 3 M
  have hAO : A ≤ Subgroup.normalizer (O : Set G) := hAM.trans hMO
  have hSO' : S ≤ Subgroup.normalizer (O : Set G) := hSO.trans Subgroup.le_normalizer
  obtain ⟨T, hTsyl, hST, hAT'⟩ := exists_isSylowOf_le_of_coprime189 hA3grp hAO hO3 hSO hS2 hAT
  have hTmem : T ∈ invariantPiSubgroups ⊤ A (piOf 2) :=
    (mem_invariantPiSubgroups_piOf_iff Nat.prime_two).mpr ⟨le_top, hTsyl.isPGroup, hAT'⟩
  have hTS : T = S := le_antisymm (hSmax'.2 hTmem hST) hST
  have hSyl : CFSG.ABGLocalTools.IsSylowOf 2 S O := by
    rw [← hTS]
    exact hTsyl
  have hON : O ≤ Subgroup.normalizer (L : Set G) :=
    h187 G A M H' c hsec h7 O
      ((mem_invariantPiSubgroups_piCompl_iff Nat.prime_three).mpr ⟨le_top, hO3, sup_le hAO hSO'⟩)
  have hMN : M ≤ Subgroup.normalizer (L : Set G) :=
    (le_sup_normalizer_of_isSylowOf hSyl hMO).trans (sup_le hON hNS)
  have hMmax : CFSG.IsMaximalTwoLocal M := hstd.mem_scriptM.1
  have hNM : Subgroup.normalizer (L : Set G) ≤ M := by
    by_contra hlt
    exact hMmax.2 _ (lt_of_le_of_ne hMN (fun h => hlt h.symm.le)) hmaxN.1
  have hLM : L ≤ M := le_trans Subgroup.le_normalizer hNM
  exact perfectResidual_not_le_of_mem_scriptH hstd h7.1.prop hLM

end CFSG.RankThree.PartTwo.Sec18
