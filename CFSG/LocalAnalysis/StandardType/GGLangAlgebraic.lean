module

public import CFSG.HardMathSupport.Timmesfeld.LangTorus.RigidDescent
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerE8Five
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerResiduals
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwE6
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwF4
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.LangTorusSylowFree
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.CrossLin
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.LangFrame
public import CFSG.LieType.AlgebraicGroups.ConnectedToralLang
public import CFSG.LieType.Chevalley.EvenTrialityOuterInvolutions
public import CFSG.LieType.Chevalley.OddTrialityCosetInvolutions
public import CFSG.LieType.SeitzGeneration.ExtSeitzReeF4Cyclic
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsCentModel
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsFieldAut
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueUStatement
public import CFSG.LocalAnalysis.ComponentClassification.GSLitType
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpExclusion
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrCentralSylowMaximality
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSAContainedSource
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedLayerOddCoreUnbalancingTriple
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenOrthogonalModel
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.TypeB2
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.Unitary
public import CFSG.RankThree.CentralLiftSO.SplitTorusWeyl
public import CFSG.RankThree.Chevalley.SteinbergBTTwistedCosetDescent
public import CFSG.RankThree.Classical.SteinbergBJSymplecticSquareZeroCentralizer
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
public import CFSG.RankThree.PartOne.S11d.OutLinear
public import CFSG.RankThree.PartTwo.KFacts.KS14SzLie
public import CFSG.RankThree.PartTwo.Sec4.Census.Interface
public import CFSG.RankThree.SteinbergR3EOrthogonalCoprimeCyclic
public import CFSG.SignalizerFunctorTheorem.Nonsolvable.SolComponent
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
public import Certificates.Certificate1
public import Certificates.Certificate2

public section

namespace CFSG.StandardType

open CFSG.Blueprint.Chevalley CFSG.HardMathSupport.Timmesfeld.LangTorus

theorem langSetup_isAlgebraic_of_zmod_two
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L]
    [Algebra (ZMod 2) L] [Algebra.IsAlgebraic (ZMod 2) L] {p₀ f : ℕ}
    (S : LangSetup τ L p₀) (hq : S.D.q = 2 ^ f) : S.IsAlgebraic := by
  classical
  intro c
  have hint : IsIntegral (ZMod 2) c := (Algebra.IsAlgebraic.isAlgebraic c).isIntegral
  have : FiniteDimensional (ZMod 2) (IntermediateField.adjoin (ZMod 2) {c}) :=
    IntermediateField.adjoin.finiteDimensional hint
  have : Finite (IntermediateField.adjoin (ZMod 2) {c}) := Module.finite_of_finite (ZMod 2)
  letI : Fintype (IntermediateField.adjoin (ZMod 2) {c}) := Fintype.ofFinite _
  have hcard0 : Fintype.card (IntermediateField.adjoin (ZMod 2) {c}) =
      Fintype.card (ZMod 2) ^ Module.finrank (ZMod 2) (IntermediateField.adjoin (ZMod 2) {c}) :=
    Module.card_eq_pow_finrank
  have hcard : Fintype.card (IntermediateField.adjoin (ZMod 2) {c}) =
      2 ^ Module.finrank (ZMod 2) (IntermediateField.adjoin (ZMod 2) {c}) := by
    rw [hcard0, ZMod.card]
  have hpos : 0 < Module.finrank (ZMod 2) (IntermediateField.adjoin (ZMod 2) {c}) :=
    Module.finrank_pos
  refine ⟨Module.finrank (ZMod 2) (IntermediateField.adjoin (ZMod 2) {c}), hpos, ?_⟩
  have h1 := FiniteField.pow_card_pow f
    (⟨c, IntermediateField.mem_adjoin_simple_self (ZMod 2) c⟩ :
      IntermediateField.adjoin (ZMod 2) {c})
  rw [hcard] at h1
  have h2 := congrArg (fun x : IntermediateField.adjoin (ZMod 2) {c} => (x : L)) h1
  rw [hq, ← pow_mul, mul_comm, pow_mul]
  simpa using h2

end CFSG.StandardType
