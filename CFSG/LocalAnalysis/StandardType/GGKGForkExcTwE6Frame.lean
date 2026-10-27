module

public import CFSG.LocalAnalysis.StandardType.GGKGForkExcFrame
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerFiveLang
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerResiduals
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwE6
public import CFSG.LieType.SeitzGeneration.ExtSeitzReeF4Cyclic
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsCentModel
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsFieldAut
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.TypeB2
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.Unitary
public import CFSG.RankThree.CentralLiftSO.SplitTorusWeyl
public import CFSG.RankThree.Chevalley.SteinbergBTTwistedCosetDescent
public import CFSG.RankThree.PartOne.BRANCH.RankRee
public import CFSG.RankThree.PartOne.CTP.StrongPBridgeRest
public import CFSG.RankThree.PartOne.KC.LinearCommutatorOdd
public import CFSG.RankThree.PartOne.KC.LinearDegreeFive
public import CFSG.RankThree.PartOne.KC.OrthogonalD4WitnessEven
public import CFSG.RankThree.PartOne.KC.OrthogonalD4WitnessOdd
public import CFSG.RankThree.PartOne.KC.UnitaryHigherCrossPrimeTorus
public import CFSG.RankThree.PartOne.KC.UnitaryPlaneEndpoints
public import CFSG.RankThree.PartOne.KD4T.Certs
public import CFSG.RankThree.PartOne.KE.StabGeneral
public import CFSG.RankThree.PartOne.N143.Weyl613Defs
public import CFSG.RankThree.PartOne.N143X.KF64WSimple
public import CFSG.RankThree.PartOne.S11d.OutExceptional
public import CFSG.RankThree.PartTwo.KFacts.KS14SzLie
public import CFSG.RankThree.PartTwo.Sec4.Census.Interface

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.PartOne.KE
  CFSG.LieType.AlgebraicGroups

structure TwE6Frame
    (K : Type) [Field K] [Finite K] (σ : K ≃+* K) (n p : ℕ)
    (E : Subgroup (twistedE6RootGroup K σ)) where
  Fr : AlgebraicClosure K →+* AlgebraicClosure K
  v : WeylGroup TwistTag.E6.tag
  g0 : ModGL TwistTag.E6.tag (AlgebraicClosure K)
  fr_eq : ∀ c, Fr c = c ^ (2 ^ n)
  g0_mem : g0 ∈ adjointGroup TwistTag.E6.tag (AlgebraicClosure K)
  lang : twistHom TwistTag.E6 (AlgebraicClosure K) Fr g0 =
    g0 * canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) v
  mem_iff : ∀ x : twistedE6RootGroup K σ, x ∈ E ↔ x ^ p = 1 ∧
    g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL TwistTag.E6.tag K) * g0 ∈
      twistedTorusOf (canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) v)
        (twistHom TwistTag.E6 (AlgebraicClosure K) Fr)

@[expose] def TwE6SCTorusInput
    (K : Type) [Field K] [Finite K] (σ : K ≃+* K) (n p r₀ : ℕ) :
    Prop :=
  ∀ E : Subgroup (twistedE6RootGroup K σ), IsElemAbelian p E → p ^ 3 ≤ Nat.card E →
    p ^ r₀ ≤ Nat.card E →
    (∀ g : twistedE6RootGroup K σ, (∀ e ∈ E, g * e = e * g) → g ^ p = 1 → g ∈ E) →
    ∃ F : TwE6Frame K σ n p E, (p ∣ 2 ^ n - 1 → F.v = 1) ∧
      (p ∣ 2 ^ n + 1 → ExcIsLongest TwistTag.E6.tag F.v)

end CFSG.StandardType

end
