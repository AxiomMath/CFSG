module

public import CFSG.HardMathSupport.Timmesfeld.LangTorus.CentralizerTrivialQ2
public import CFSG.LieType.Chevalley.RootCharacterConjugation
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerE8Five
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerResiduals
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwE6
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwF4
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwRigid
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.CentralizerTrivialPoly
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.CentralizerTrivialQ3T
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.OuterField
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.RigidField
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
public import CFSG.LocalAnalysis.ComponentInitial.CentralCoverAbelian
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

namespace CFSG.StandardType.LangRat

section DetectsTwoE

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus
open scoped commutatorElement


theorem langRatCentralizerDetects_two_inner_E
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ} (S : LangSetup τ L p₀)
    (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) (hq : S.D.q = 2)
    {a b : Fin τ.rank → Lˣ} (ha : rootDiagUnit τ a ∈ S.D.torus)
    (hb : rootDiagUnit τ b ∈ S.D.torus) (i : KernelComponent (rootCharHom a))
    (hinner : twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ (componentRoots (rootCharHom a) i)]))
    (hs1 : componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) = 1)
    (hrk : 2 < (componentRoots (rootCharHom a) i).ncard)
    (hle : rationalComponent S.ρ S.Γ (rootCharHom a) i ≤ Subgroup.centralizer {rootDiagUnit τ b}) :
    ∀ γ ∈ rationalRoots S.ρ (rootCharHom a) i, rootChar b γ = 1 := by
  have hcomm : ∀ x ∈ rationalComponent S.ρ S.Γ (rootCharHom a) i,
      Commute (rootDiagUnit τ b) x :=
    fun x hx => (Subgroup.mem_centralizer_singleton_iff.1 (hle hx)).symm
  have hspan := commute_rootSpan_of_commute_component_two S hτ ha i hinner hs1 hq hrk
    (rootDiagUnit τ b) hcomm
  have hcomp : ∀ δ ∈ componentRoots (rootCharHom a) i, rootChar b δ = 1 := by
    intro δ hδ
    have hδr : IsRoot τ δ := hδ.1.1
    have hmem := pinnedX_mem_rootSpan (K := L) (S := componentRoots (rootCharHom a) i) hδ (1 : L)
    have hc := hspan _ hmem
    have hconj := rootDiagUnit_conj_pinnedX (τ := τ) (K := L) b hδr 1
    have hcomm' : rootDiagUnit τ b * pinnedX τ L δ 1 * (rootDiagUnit τ b)⁻¹ = pinnedX τ L δ 1 := by
      rw [hc.eq]
      group
    rw [hcomm'] at hconj
    have h1 := pinnedX_injective (τ := τ) (R := L) δ hconj
    exact Units.ext (by simpa using h1.symm)
  rintro γ ⟨k, δ, hδ, rfl⟩
  have key : ∀ k : ℕ, rootChar b ((S.ρ : (Fin τ.rank → ℤ) → _)^[k] δ) = 1 ∧
      IsRoot τ ((S.ρ : (Fin τ.rank → ℤ) → _)^[k] δ) := by
    intro k
    induction k with
    | zero => exact ⟨hcomp δ hδ, hδ.1.1⟩
    | succ k ih =>
      rw [Function.iterate_succ_apply']
      exact ⟨by rw [S.frob.rootChar_eq b hb _ ih.2, ih.1, one_pow], (S.frob.isRoot_iff _).2 ih.2⟩
  exact (key k).1

end DetectsTwoE

end CFSG.StandardType.LangRat
