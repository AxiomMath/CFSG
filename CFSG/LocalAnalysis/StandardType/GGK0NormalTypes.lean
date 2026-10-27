module

public import CFSG.LocalAnalysis.StandardType.GGK0NormalForm
import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompSUE6
import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompSUE7
import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompSUE8
import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompSUF4
public import CFSG.Sporadic.ThSchreier.GlobalData
public import CFSG.Sporadic.ThSchreier.LocalOrbitBase1
import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerE8Five
import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerResiduals
import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwE6
import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwF4
import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwRigid
import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompSU
import CFSG.HardMathSupport.Timmesfeld.LangTorus.CentralizerTrivialPoly
import CFSG.HardMathSupport.Timmesfeld.LangTorus.OuterField
import CFSG.HardMathSupport.Timmesfeld.LangTorus.RigidField
import CFSG.HardMathSupport.Timmesfeld.LangTorus.RigidNorm
import CFSG.HardMathSupport.Timmesfeld.LocalTwo.LangFrame
import CFSG.LieType.AlgebraicGroups.ConnectedToralLang
import CFSG.LieType.Chevalley.C2E6UnitaryFourImages
import CFSG.LieType.Chevalley.EvenTrialityOuterInvolutions
import CFSG.LieType.Chevalley.OddTrialityCosetInvolutions
import CFSG.LieType.SeitzGeneration.ExtSeitzReeF4Cyclic
import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsCentModel
import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsFieldAut
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixStructure
import CFSG.LocalAnalysis.ComponentClassification.CatalogueUStatement
import CFSG.LocalAnalysis.ComponentClassification.GSLitType
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpExclusion
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrCentralSylowMaximality
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSAContainedSource
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedLayerOddCoreUnbalancingTriple
import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenOrthogonalModel
import CFSG.LocalAnalysis.QuasithinUnique.SQTK.TypeB2
import CFSG.LocalAnalysis.QuasithinUnique.SQTK.Unitary
import CFSG.RankThree.CentralLiftSO.SplitTorusWeyl
import CFSG.RankThree.Chevalley.SteinbergBID4CentralKernel
import CFSG.RankThree.Chevalley.SteinbergBTTwistedCosetDescent
import CFSG.RankThree.Classical.SteinbergBJSymplecticSquareZeroCentralizer
import CFSG.RankThree.Classical2.TwistedE6Phi3A2Case
import CFSG.RankThree.PartOne.BRANCH.RankRee
import CFSG.RankThree.PartOne.CTP.StrongPBridgeRest
import CFSG.RankThree.PartOne.KC.LinearCommutatorOdd
import CFSG.RankThree.PartOne.KC.LinearDegreeFive
import CFSG.RankThree.PartOne.KC.OrthogonalD4WitnessEven
import CFSG.RankThree.PartOne.KC.OrthogonalD4WitnessOdd
import CFSG.RankThree.PartOne.KC.UnitaryHigherCrossPrimeTorus
import CFSG.RankThree.PartOne.KC.UnitaryPlaneEndpoints
import CFSG.RankThree.PartOne.KE.E7FiveBlock
import CFSG.RankThree.PartOne.KE.E8D4Family
import CFSG.RankThree.PartOne.KE.ThreeA1Group
import CFSG.RankThree.PartOne.KLCE.Sector
import CFSG.RankThree.PartOne.N143.Weyl613Defs
import CFSG.RankThree.PartOne.N143X.KF64WSimple
import CFSG.RankThree.PartOne.S11d.OutExceptional
import CFSG.RankThree.PartOne.S11d.OutLinear
import CFSG.RankThree.PartTwo.KFacts.KS14SzLie
import CFSG.RankThree.PartTwo.Sec4.Census.Interface
import CFSG.RankThree.SteinbergR3EOrthogonalCoprimeCyclic
import CFSG.SignalizerFunctorTheorem.Nonsolvable.SolComponent
import CFSG.Sporadic.Schreier.J4SProfileNode
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
import Certificates.Certificate1
import Certificates.Certificate1953
import Certificates.Certificate1954
import Certificates.Certificate2
import Certificates.Kernel.SporSch.Th.Plane2320

public section

namespace CFSG.StandardType.GGK0MarkedKacIface1587

open CFSG CFSG.Assembly CFSG.StandardType
open CFSG.HardMathSupport.Timmesfeld.CrossChar
open CFSG.Blueprint.Chevalley

variable {Omega : Type} [Field Omega] [IsAlgClosed Omega] [CharP Omega 2]
  {lab : LargeEvenLabel} {p : ℕ} {R : Type} [Group R] {I : Set (MulAut R)} {phi : MulAut R}

omit [CharP Omega 2] in
private theorem exists_normal_of_tag (T : GGKacType) (τ : Tag) (h : absTag T = τ) :
    ∃ K : KacData τ, K.Facts ∧ (k0DiagOf T).marks.length = τ.rank + 1 ∧
      (k0DiagOf T).marks.getD 0 0 = 1 ∧
      (∀ j : Fin τ.rank, K.θ j = ((k0DiagOf T).marks.getD (j.val + 1) 0 : ℤ)) ∧
      ∀ i j, i < τ.rank + 1 → j < τ.rank + 1 →
        (K.Adj (idxNode i) (idxNode j) ↔ 0 < (k0DiagOf T).adj i j) := by
  subst h
  cases T
  all_goals dsimp only [absTag]
  · refine ⟨kacE6, facts_E6, by decide, by decide, fun j => by fin_cases j <;> rfl, ?_⟩
    intro i j hi hj
    rw [e6_adj, nodeIdx_idxNode hi, nodeIdx_idxNode hj]
    have hi' : i < 7 := by rw [show Tag.E6.rank = 6 from rfl] at hi; omega
    have hj' : j < 7 := by rw [show Tag.E6.rank = 6 from rfl] at hj; omega
    interval_cases i <;> interval_cases j <;> decide
  · refine ⟨kacE7, facts_E7, by decide, by decide, fun j => by fin_cases j <;> rfl, ?_⟩
    intro i j hi hj
    rw [e7_adj, nodeIdx_idxNode hi, nodeIdx_idxNode hj]
    have hi' : i < 8 := by rw [show Tag.E7.rank = 7 from rfl] at hi; omega
    have hj' : j < 8 := by rw [show Tag.E7.rank = 7 from rfl] at hj; omega
    interval_cases i <;> interval_cases j <;> decide
  · refine ⟨kacE8, facts_E8, by decide, by decide, fun j => by fin_cases j <;> rfl, ?_⟩
    intro i j hi hj
    rw [e8_adj, nodeIdx_idxNode hi, nodeIdx_idxNode hj]
    have hi' : i < 9 := by rw [show Tag.E8.rank = 8 from rfl] at hi; omega
    have hj' : j < 9 := by rw [show Tag.E8.rank = 8 from rfl] at hj; omega
    interval_cases i <;> interval_cases j <;> decide
  · refine ⟨kacF4, facts_F4, by decide, by decide, fun j => by fin_cases j <;> rfl, ?_⟩
    intro i j hi hj
    rw [f4_adj, nodeIdx_idxNode hi, nodeIdx_idxNode hj]
    have hi' : i < 5 := by rw [show Tag.F4.rank = 4 from rfl] at hi; omega
    have hj' : j < 5 := by rw [show Tag.F4.rank = 4 from rfl] at hj; omega
    interval_cases i <;> interval_cases j <;> decide

omit [CharP Omega 2] in
theorem k0Normal_nonempty (A : K0LangMark Omega lab p R I phi) : Nonempty (K0Normal A) := by
  obtain ⟨K, hfacts, hlen, hzero, hθ, hadj⟩ :=
    exists_normal_of_tag A.row.T A.tau A.tau_eq
  exact ⟨⟨K, hfacts, hlen, hzero, hθ, hadj⟩⟩

end CFSG.StandardType.GGK0MarkedKacIface1587

end
