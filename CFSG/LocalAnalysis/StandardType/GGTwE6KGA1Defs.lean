module

public import CFSG.HardMathSupport.Lang.E6Descent.OuterFixed27TwistedE6Core
public import CFSG.LocalAnalysis.StandardType.GGTableBExcE6ThreeAd
public import CFSG.Blueprint.ChevalleyRootArtifact
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.CentralResidueMaps
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.NormalizerClassLifting
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.PrincipalClassDefects
public import CFSG.CharacterTheory.Semidihedral.Principal.DegreeZeroGram
public import CFSG.CharacterTheory.TwoRankLowerBound.BrauerCharacterCriterion
public import CFSG.HardMathSupport.Lang.Coordinator.OuterFixedOrderTwistedE6Fixed
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
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrCriticalStandard
public import CFSG.RankThree.PartOne.SLB4A.ClassExcRest
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

public noncomputable section

namespace CFSG.StandardType.NoOffTwE6Three

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.Classical2
  CFSG.HardMathSupport.Lang.E6Descent CFSG.Open


@[expose] def IsToralE6 (Ω : Type) [Field Ω] (X : Subgroup (ModGL Tag.E6 Ω)) : Prop :=
  ∃ h ∈ adjointGroup Tag.E6 Ω, ∀ x ∈ X, h⁻¹ * x * h ∈ torusGroup Tag.E6 Ω

@[expose] def GGTwE6ThreeTwoLocalInnToralInput : Prop :=
  ∀ {f : ℕ}, 1 ≤ f → 3 ∣ 2 ^ f + 1 →
    ∀ (Ω : Type) [Field Ω] [Algebra (GaloisField 2 (2 * f)) Ω]
      [IsAlgClosure (GaloisField 2 (2 * f)) Ω] (Fr : Ω →+* Ω), (∀ c, Fr c = c ^ 2 ^ f) →
    ∀ {X V : Subgroup (ModGL Tag.E6 Ω)}, X ≤ TwistedDiag.Rgrp Ω Fr → V ≤ TwistedDiag.Rgrp Ω Fr →
      IsElemAbelian 3 X → Nat.card X = 3 ^ 4 → V ≠ ⊥ → IsPGroup 2 V →
      X ≤ Subgroup.normalizer (V : Set _) → IsToralE6 Ω X

@[expose] def GGTwE6ThreeToralTypeMinusOneInput : Prop :=
  ∀ {f : ℕ}, 1 ≤ f → 3 ∣ 2 ^ f + 1 →
    ∀ (Ω : Type) [Field Ω] [Algebra (GaloisField 2 (2 * f)) Ω]
      [IsAlgClosure (GaloisField 2 (2 * f)) Ω] (Fr : Ω →+* Ω), (∀ c, Fr c = c ^ 2 ^ f) →
    ∀ {ζ : Ωˣ} (hζ : ζ ^ 3 = 1), orderOf ζ = 3 →
    ∀ {X : Subgroup (ModGL Tag.E6 Ω)}, X ≤ TwistedDiag.Rgrp Ω Fr → IsElemAbelian 3 X →
      Nat.card X = 3 ^ 4 → IsToralE6 Ω X →
      ∃ g ∈ adjointGroup Tag.E6 Ω, g⁻¹ * twistE6 Ω Fr g = TwistedDiag.n0 Ω ∧
        ∀ x ∈ X, ∃ v, x = g * rootDiagUnit Tag.E6
          (CFSG.StandardType.TableBExc.E6Three.zetaVec ζ hζ v) * g⁻¹

end CFSG.StandardType.NoOffTwE6Three
