module

public import CFSG.LocalAnalysis.StandardType.FF81.CatQ1.Defs
public import CFSG.LocalAnalysis.StandardType.FF81.CatQ1.Arith
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongOFRCOrthOdd
public import CFSG.LocalAnalysis.SectionRank.ClassicalOdd
public import CFSG.Open.StatedDefs
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.CentralResidueMaps
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.NormalizerClassLifting
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.PrincipalClassDefects
public import CFSG.CharacterTheory.Semidihedral.Principal.DegreeZeroGram
public import CFSG.CharacterTheory.TwoRankLowerBound.BrauerCharacterCriterion
public import CFSG.HardMathSupport.Lang.UnitaryAutomorphisms.OuterFixedPOmegaEven
public import CFSG.LieType.Ree.SuzukiSimple
public import CFSG.LieType.Steinberg.Classical.SpinFrame
public import CFSG.LieType.Steinberg.Families
public import CFSG.LieType.Universal.Spin.Generation
public import CFSG.LieType.Universal.Spin.OddCT
public import CFSG.LieType.Universal.Spin.PlusCT
public import CFSG.LieType.Universal.Spin.Structure
public import CFSG.LieType.Universal.SpinOmega
public import CFSG.LieType.Universal.Unitary
public import CFSG.LinearAlgebra.LinearGroups.CoordinateData
public import CFSG.LocalAnalysis.ComponentClassification.BlockCentralSylowEquality
public import CFSG.LocalAnalysis.ComponentClassification.BlockFourFactorSupport
public import CFSG.LocalAnalysis.ComponentClassification.BlockLargeProductInvolutions
public import CFSG.LocalAnalysis.ComponentClassification.BlockMovedFactorSylowCentral
public import CFSG.LocalAnalysis.ComponentClassification.BlockNormalizerOrder
public import CFSG.LocalAnalysis.ComponentClassification.BlockPermutationSylowLifting
public import CFSG.LocalAnalysis.ComponentClassification.BlockStrictFullSylowAbelian
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeMax
public import CFSG.LocalAnalysis.ComponentClassification.KProper
public import CFSG.LocalAnalysis.ComponentClassification.LabeledBlockPermutation
public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalOddCentralizer
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenCanonicalField
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrCriticalStandard
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.SectionRank.Ccomm.Supercritical
public import CFSG.LocalAnalysis.SectionRank.EvenCover.LinearStep
public import CFSG.LocalAnalysis.SectionRank.SporadicCover
public import CFSG.RankThree.CentralLiftSO.SplitTorusWeyl
public import CFSG.RankThree.PartOne.KC.LinearDegreeFive
public import CFSG.RankThree.PartOne.KC.LinearSplitInner
public import CFSG.RankThree.PartOne.KC.OrthogonalFieldDescent
public import CFSG.RankThree.PartOne.KC.SymplecticOrthogonalNoninner
public import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeOrbits
public import CFSG.RankThree.PartOne.KC.UnitaryPlaneEndpoints
public import CFSG.RankThree.SteinbergR3EOrthogonalCoprimeCyclic
public import CFSG.RankThree.Theta.ThreeComponentOrbitCover
public import CFSG.Sporadic.M23.M23Group
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
public import TauCeti.LinearAlgebra.CliffordAlgebra.Monomials

public section

namespace CFSG.StandardType.FF81.CatQ1

open CFSG.Open
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD291OL
open CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD291OL.OFRC

private theorem four_le_pRank_statedProj_POmegaOdd_charThree {n f₀ : ℕ} (hn : 3 ≤ n)
    (hf₀ : 1 ≤ f₀) {F₀ : Type} [Field F₀] [Finite F₀] (hF₀ : Nat.card F₀ = 3 ^ f₀) :
    4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (StatedProj (StatedOmega (StatedQuadOdd n F₀)))) := by
  have hm : StatedClassicalModel (StatedProj (StatedOmega (StatedQuadOdd n F₀))) .POmegaOdd n 3
      f₀ := ⟨⟨Nat.prime_three, hf₀, hn, by norm_num⟩, F₀, inferInstance, inferInstance, hF₀,
        ⟨MulEquiv.refl _⟩⟩
  obtain ⟨-, -, hcases⟩ :=
    CFSG.SectionRank.classical_model_rank (by norm_num : (3 : ℕ) ≠ 2) hm
  rcases hcases with ⟨ht, -⟩ | ⟨ht, -⟩ | ⟨ht, -⟩ | h1
  · exact absurd ht (by decide)
  · exact absurd ht (by decide)
  · exact absurd ht (by decide)
  · exact h1

theorem outerThreeBig_of_modelPOmegaOdd {K : Type} [Group K] [Finite K] {n ℓ f : ℕ}
    (hcl : StatedClassicalModel K .POmegaOdd n ℓ f) : OuterThreeBig K := by
  intro h4 β hβ hout
  have hin : β ∉ inner K := by
    rintro ⟨k, hk⟩
    exact hout k hk.symm
  obtain ⟨hpf, F₀, hF₀, hF₀fin, hcard, hrank⟩ :=
    pomegaOdd_pRank_fixed hcl Nat.prime_three (by norm_num) β hβ hin
  obtain ⟨⟨hℓp, hf, hn, hℓ2⟩, F, hF, hFin, hFcard, ⟨e⟩⟩ := hcl
  refine Or.inl ?_
  refine twentySeven_dvd_of_three_le_pRank (fixedSubgroup β) ?_
  by_cases hℓ3 : ℓ = 3
  ·
    have hfp : 1 ≤ f / 3 :=
      Nat.div_pos (Nat.le_of_dvd (by omega) hpf) (by norm_num)
    have hcard3 : Nat.card F₀ = 3 ^ (f / 3) := by rw [hcard, hℓ3]
    have h1 := four_le_pRank_statedProj_POmegaOdd_charThree hn hfp hcard3
    omega
  ·
    have hFcard' : Nat.card F = Nat.card F₀ ^ 3 := by
      rw [hFcard, hcard, ← pow_mul, Nat.div_mul_cancel hpf]
    have hpF : ¬ 3 ∣ Nat.card F := by
      rw [hFcard]
      exact not_dvd_pow_of_ne Nat.prime_three hℓp hℓ3
    have hF2 : (2 : F) ≠ 0 := by
      have h := natCast_ne_zero_of_not_dvd_card (F := F) (p := 2) Nat.prime_two
        (by rw [hFcard]; exact not_dvd_pow_of_ne Nat.prime_two hℓp hℓ2)
      exact_mod_cast h
    have hF₀2 : (2 : F₀) ≠ 0 := by
      have h := natCast_ne_zero_of_not_dvd_card (F := F₀) (p := 2) Nat.prime_two
        (by rw [hcard]; exact not_dvd_pow_of_ne Nat.prime_two hℓp hℓ2)
      exact_mod_cast h
    have hK := CFSG.SectionRank.pRank_top_eq_of_mulEquiv (show 1 < 3 by norm_num) e
    have heq := pRank_statedProj_OmegaOdd_eq_of_pow (F := F) (F₀ := F₀) (n := n)
      Nat.prime_three (by norm_num) hn hF2 hF₀2 hFcard' hpF
    omega

end CFSG.StandardType.FF81.CatQ1
