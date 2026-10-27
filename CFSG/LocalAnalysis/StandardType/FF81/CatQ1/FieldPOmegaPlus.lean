module

public import CFSG.LocalAnalysis.StandardType.FF81.CatQ1.Defs
public import CFSG.Open.StatedDefs
import CFSG.LocalAnalysis.StandardType.FF81.CatQ1.Arith
import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongOFRCOrthPlus
import CFSG.Assembly.OrderReductions.InvertedSubgroup
import CFSG.Assembly.OrderReductions.OddInversion
import CFSG.CharacterTheory.BrauerThirdMainTheorem.CentralResidueMaps
import CFSG.CharacterTheory.BrauerThirdMainTheorem.NormalizerClassLifting
import CFSG.CharacterTheory.BrauerThirdMainTheorem.PrincipalClassDefects
import CFSG.CharacterTheory.Semidihedral.Principal.DegreeZeroGram
import CFSG.CharacterTheory.TwoRankLowerBound.BrauerCharacterCriterion
import CFSG.HardMathSupport.Lang.UnitaryAutomorphisms.OuterFixedPOmegaEven
import CFSG.LieType.Ree.SuzukiSimple
import CFSG.LieType.Steinberg.Classical.SpinFrame
import CFSG.LieType.Steinberg.Families
import CFSG.LieType.Universal.Spin.Generation
import CFSG.LieType.Universal.Spin.OddCT
import CFSG.LieType.Universal.Spin.PlusCT
import CFSG.LieType.Universal.Spin.Structure
import CFSG.LieType.Universal.SpinOmega
import CFSG.LieType.Universal.Unitary
import CFSG.LinearAlgebra.LinearGroups.CoordinateData
import CFSG.LocalAnalysis.ComponentClassification.BlockCentralSylowEquality
import CFSG.LocalAnalysis.ComponentClassification.BlockFourFactorSupport
import CFSG.LocalAnalysis.ComponentClassification.BlockLargeProductInvolutions
import CFSG.LocalAnalysis.ComponentClassification.BlockMovedFactorSylowCentral
import CFSG.LocalAnalysis.ComponentClassification.BlockNormalizerOrder
import CFSG.LocalAnalysis.ComponentClassification.BlockPermutationSylowLifting
import CFSG.LocalAnalysis.ComponentClassification.BlockStrictFullSylowAbelian
import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeMax
import CFSG.LocalAnalysis.ComponentClassification.KProper
import CFSG.LocalAnalysis.ComponentClassification.LabeledBlockPermutation
import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalOddCentralizer
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenCanonicalField
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrCriticalStandard
import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
import CFSG.LocalAnalysis.SectionRank.Ccomm.Supercritical
import CFSG.LocalAnalysis.SectionRank.EvenCover.LinearStep
import CFSG.LocalAnalysis.SectionRank.SporadicCover
import CFSG.RankThree.CentralLiftSO.SplitTorusWeyl
import CFSG.RankThree.PartOne.KC.LinearDegreeFive
import CFSG.RankThree.PartOne.KC.LinearSplitInner
import CFSG.RankThree.PartOne.KC.OrthogonalFieldDescent
import CFSG.RankThree.PartOne.KC.SymplecticOrthogonalNoninner
import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeOrbits
import CFSG.RankThree.PartOne.KC.UnitaryPlaneEndpoints
import CFSG.RankThree.SteinbergR3EOrthogonalCoprimeCyclic
import CFSG.RankThree.Theta.ThreeComponentOrbitCover
import CFSG.Sporadic.M23.M23Group
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldPrimeOrderFixedSubfield
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.OrderThreeNormalizer
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGammaL2PSLRangeCentralizer
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinInvolutionCount
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinRestrictionSixCount
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinUDecomposition
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationEleven
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationTen
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationTenStructuralIdentities
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2FieldProjectionArithmetic
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2OrderPSubgroupCount
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Suzuki.OddGraphReconstruction
import Certificates.Certificate1
import Certificates.Certificate10
import Certificates.Certificate11
import Certificates.Certificate12
import Certificates.Certificate2
import Certificates.Certificate3
import Certificates.Certificate4
import Certificates.Certificate42
import Certificates.Certificate44
import Certificates.Certificate5
import Certificates.Certificate6
import Certificates.Certificate7
import Certificates.Certificate8
import Certificates.Certificate9
import TauCeti.LinearAlgebra.CliffordAlgebra.Monomials

public section

namespace CFSG.StandardType.FF81.CatQ1

open CFSG.Open
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD291OL

theorem outerThreeBig_of_modelPOmegaPlus {K : Type} [Group K] [Finite K] {n ℓ f : ℕ}
    (hn : 5 ≤ n) (hcl : StatedClassicalModel K .POmegaPlus n ℓ f) : OuterThreeBig K := by
  intro h4 β hβ hout
  have hin : β ∉ CFSG.ComponentClassification.OuterAutomorphisms.inner K := by
    rintro ⟨k, hk⟩
    exact hout k hk.symm
  obtain ⟨hpf, F₀, hF₀, hF₀fin, hcard, hrank⟩ :=
    pomegaPlus_pRank_fixed hcl Nat.prime_three (by norm_num) (fun h => by omega) β hβ hin
  obtain ⟨⟨hℓp, hf, -⟩, F, hF, hFin, hFcard, ⟨e⟩⟩ := hcl
  refine Or.inl (twentySeven_dvd_of_three_le_pRank (fixedSubgroup β) ?_)
  by_cases hℓ3 : ℓ = 3
  ·
    have hcard3 : Nat.card F₀ = 3 ^ (f / 3) := by simpa [hℓ3] using hcard
    have hf3 : 1 ≤ f / 3 := Nat.div_pos (Nat.le_of_dvd (by omega) hpf) (by norm_num)
    have hm : StatedClassicalModel (StatedProj (StatedOmega (StatedQuadPlus n F₀))) .POmegaPlus
        n 3 (f / 3) :=
      ⟨⟨Nat.prime_three, hf3, by omega⟩, F₀, hF₀, hF₀fin, hcard3, ⟨MulEquiv.refl _⟩⟩
    obtain ⟨-, -, hcases⟩ := CFSG.SectionRank.classical_model_rank (by norm_num) hm
    rcases hcases with ⟨ht, -⟩ | ⟨ht, -⟩ | ⟨ht, -⟩ | h1
    · exact absurd ht (by decide)
    · exact absurd ht (by decide)
    · exact absurd ht (by decide)
    · omega
  ·
    have hFcard' : Nat.card F = Nat.card F₀ ^ 3 := by
      rw [hFcard, hcard, ← pow_mul, Nat.div_mul_cancel hpf]
    have hpF : ¬ 3 ∣ Nat.card F := by
      rw [hFcard]
      exact CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD291OL.OFRC.not_dvd_pow_of_ne
        Nat.prime_three hℓp hℓ3
    have hKtop : CFSG.Open.pRank 3 (⊤ : Subgroup K) =
        CFSG.Open.pRank 3 (⊤ : Subgroup (StatedProj (StatedOmega (StatedQuadPlus n F)))) :=
      CFSG.SectionRank.pRank_top_eq_of_mulEquiv Nat.prime_three.one_lt e
    have heq := pRank_statedProj_OmegaPlus_eq_of_pow
      (F := F) (F₀ := F₀) (n := n) Nat.prime_three (by norm_num) (by omega) hFcard' hpF
    omega

end CFSG.StandardType.FF81.CatQ1
