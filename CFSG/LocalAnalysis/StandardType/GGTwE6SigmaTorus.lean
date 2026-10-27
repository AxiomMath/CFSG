module

public import CFSG.HardMathSupport.Lang.E6Descent.OuterFixed27TwistedE6Core
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.E6ThreeToralityTw
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.CentralResidueMaps
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.NormalizerClassLifting
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.PrincipalClassDefects
public import CFSG.HardMathSupport.Lang.Coordinator.OuterFixedOrderTwistedE6Fixed
public import CFSG.LieType.Chevalley.E6GraphHighestRootNormalizer
public import CFSG.LieType.Chevalley.SimplyLacedFieldTwoCover
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
public import Certificates.Certificate10
public import Certificates.Certificate11
public import Certificates.Certificate12
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

namespace CFSG.StandardType.TwE6SigmaTorus

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.HardMathSupport.Lang.E6Descent
open CFSG.RankThree.Classical2 (twistE6)


theorem exists_sigmaTorus_of_toral {f : ℕ} (hf : 1 ≤ f) (Ω : Type) [Field Ω]
    [Algebra (GaloisField 2 (2 * f)) Ω] [IsAlgClosure (GaloisField 2 (2 * f)) Ω]
    (Fr : Ω →+* Ω) (hFr : ∀ c, Fr c = c ^ 2 ^ f) {X : Subgroup (ModGL Tag.E6 Ω)}
    (hX : X ≤ TwistedDiag.Rgrp Ω Fr)
    (hXt : ∃ h ∈ adjointGroup Tag.E6 Ω, ∀ x ∈ X, h⁻¹ * x * h ∈ torusGroup Tag.E6 Ω) :
    ∃ v : WeylGroup Tag.E6, ∃ g₀ ∈ adjointGroup Tag.E6 Ω,
      g₀⁻¹ * twistE6 Ω Fr g₀ = canonicalRep (coxeterSystem Tag.E6) Ω v ∧
        ∀ x ∈ X, g₀⁻¹ * x * g₀ ∈ torusGroup Tag.E6 Ω ∧
          canonicalRep (coxeterSystem Tag.E6) Ω v * twistE6 Ω Fr (g₀⁻¹ * x * g₀) *
            (canonicalRep (coxeterSystem Tag.E6) Ω v)⁻¹ = g₀⁻¹ * x * g₀ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed (GaloisField 2 (2 * f))
  haveI : CharP Ω 2 := charP_of_injective_algebraMap
    (algebraMap (GaloisField 2 (2 * f)) Ω).injective 2
  have hFr' : Fr = iterateFrobenius Ω 2 f := RingHom.ext fun c => by
    rw [hFr, iterateFrobenius_def]
  subst hFr'
  obtain ⟨h, hh, hht⟩ := hXt
  have hFix : ∀ x ∈ X, twistHom TwistTag.E6 Ω (iterateFrobenius Ω 2 f) x = x := fun x hx =>
    ((TwistedDiag.mem_Rgrp _).1 (hX hx)).2
  obtain ⟨v, g₀, hg₀, hF, hA⟩ :=
    CFSG.HardMathSupport.Timmesfeld.CrossChar.exists_lang_torus_of_conj_torus_twisted 2
      TwistTag.E6 f hf hFix hh hht
  refine ⟨v, g₀, hg₀, inv_mul_eq_iff_eq_mul.2 hF, fun x hx => ?_⟩
  obtain ⟨y, hy, rfl⟩ := hA x hx
  have hy' := CFSG.RankThree.PartOne.KE.mem_twistedTorusOf.1 (SetLike.mem_coe.1 hy)
  have e : g₀⁻¹ * (MulEquiv.toMonoidHom (MulAut.conj g₀) y) * g₀ = y := by
    change g₀⁻¹ * (g₀ * y * g₀⁻¹) * g₀ = y
    group
  have h2 : g₀⁻¹ * (MulEquiv.toMonoidHom (MulAut.conj g₀) y) * g₀ ∈
        torusGroup TwistTag.E6.tag Ω ∧
      canonicalRep (coxeterSystem TwistTag.E6.tag) Ω v *
        twistHom TwistTag.E6 Ω (iterateFrobenius Ω 2 f)
          (g₀⁻¹ * (MulEquiv.toMonoidHom (MulAut.conj g₀) y) * g₀) *
        (canonicalRep (coxeterSystem TwistTag.E6.tag) Ω v)⁻¹ =
      g₀⁻¹ * (MulEquiv.toMonoidHom (MulAut.conj g₀) y) * g₀ := by
    rw [e]
    exact hy'
  exact h2

end CFSG.StandardType.TwE6SigmaTorus
