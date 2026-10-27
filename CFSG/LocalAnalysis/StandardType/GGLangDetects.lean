module

public import CFSG.HardMathSupport.Timmesfeld.LangTorus.CentralizerTrivialOuter
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.InnerQuasisimpleOrbit
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.RigidDescent
public import CFSG.LieType.Chevalley.RootCharacterConjugation
public import CFSG.LocalAnalysis.StandardType.GGLatDefs
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerE8Five
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerResiduals
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwE6
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwF4
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwRigid
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.OuterField
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.RigidField
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.RigidNorm
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
public import CFSG.RankThree.PartOne.KE.SLnShape
public import CFSG.RankThree.PartOne.KE.StabGeneral
public import CFSG.RankThree.PartOne.KGD.D4QA1
public import CFSG.RankThree.PartOne.N143.Weyl613Defs
public import CFSG.RankThree.PartOne.N143X.KF64WSimple
public import CFSG.RankThree.PartOne.S11d.OutExceptional
public import CFSG.RankThree.PartOne.S11d.OutLinear
public import CFSG.RankThree.PartTwo.KFacts.KS14SzLie
public import CFSG.RankThree.PartTwo.Sec4.Census.Interface
public import CFSG.RankThree.SteinbergR3EOrthogonalCoprimeCyclic
public import CFSG.SignalizerFunctorTheorem.Nonsolvable.SolComponent
public import CFSG.Sporadic.Th.Max3.Core
public import CFSG.Sporadic.ThSchreier.GlobalData
public import CFSG.Sporadic.ThSchreier.LocalOrbitBase1
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
public import Certificates.Certificate1
public import Certificates.Certificate2

public section

namespace CFSG.StandardType.LangRat

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus
open scoped commutatorElement

section Statements

@[expose] def LangRatCentralizerDetectsP : Prop :=
  ∀ (τ : Tag) (L : Type) [Field L] [IsAlgClosed L] (p₀ p f : ℕ) (S : LangSetup τ L p₀),
    (τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) → p.Prime → p ≠ 2 → (p : L) ≠ 0 → S.D.q = 2 ^ f →
    ∀ π : Equiv.Perm (Fin τ.rank), (∀ j k, τ.cartan (π j) (π k) = τ.cartan j k) →
    ∀ ε : ℤ, (ε = 1 ∨ ε = -1) → (∀ γ, IsRoot τ γ → S.ρ γ = ε • latPerm π γ) →
    (p : ℤ) ∣ (S.D.q : ℤ) - ε → S.IsAlgebraic →
    ∀ a b : Fin τ.rank → Lˣ,
      rootDiagUnit τ a ∈ S.D.torus → rootDiagUnit τ b ∈ S.D.torus →
      (∀ i, a i ^ p = 1) → (∀ i, b i ^ p = 1) →
      ∀ i : KernelComponent (rootCharHom a),
        CFSG.IsQuasisimple ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) →
        rationalComponent S.ρ S.Γ (rootCharHom a) i ≤ Subgroup.centralizer {rootDiagUnit τ b} →
        ∀ γ ∈ rationalRoots S.ρ (rootCharHom a) i, rootChar b γ = 1

@[expose] def LangRatCentralizerDetectsPBig : Prop :=
  ∀ (τ : Tag) (L : Type) [Field L] [IsAlgClosed L] (p₀ p f : ℕ) (S : LangSetup τ L p₀),
    (τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) → p.Prime → p ≠ 2 → (p : L) ≠ 0 → S.D.q = 2 ^ f →
    2 ≤ f →
    ∀ a b : Fin τ.rank → Lˣ,
      rootDiagUnit τ a ∈ S.D.torus → rootDiagUnit τ b ∈ S.D.torus →
      (∀ i, a i ^ p = 1) → (∀ i, b i ^ p = 1) →
      ∀ i : KernelComponent (rootCharHom a),
        CFSG.IsQuasisimple ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) →
        rationalComponent S.ρ S.Γ (rootCharHom a) i ≤ Subgroup.centralizer {rootDiagUnit τ b} →
        ∀ γ ∈ rationalRoots S.ρ (rootCharHom a) i, rootChar b γ = 1

@[expose] def LangRatCentralizerDetectsPTwo : Prop :=
  ∀ (τ : Tag) (L : Type) [Field L] [IsAlgClosed L] (p₀ p : ℕ) (S : LangSetup τ L p₀),
    (τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) → p.Prime → p ≠ 2 → (p : L) ≠ 0 → S.D.q = 2 →
    ∀ π : Equiv.Perm (Fin τ.rank), (∀ j k, τ.cartan (π j) (π k) = τ.cartan j k) →
    ∀ ε : ℤ, (ε = 1 ∨ ε = -1) → (∀ γ, IsRoot τ γ → S.ρ γ = ε • latPerm π γ) →
    (p : ℤ) ∣ (S.D.q : ℤ) - ε → S.IsAlgebraic →
    ∀ a b : Fin τ.rank → Lˣ,
      rootDiagUnit τ a ∈ S.D.torus → rootDiagUnit τ b ∈ S.D.torus →
      (∀ i, a i ^ p = 1) → (∀ i, b i ^ p = 1) →
      ∀ i : KernelComponent (rootCharHom a),
        CFSG.IsQuasisimple ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) →
        rationalComponent S.ρ S.Γ (rootCharHom a) i ≤ Subgroup.centralizer {rootDiagUnit τ b} →
        ∀ γ ∈ rationalRoots S.ρ (rootCharHom a) i, rootChar b γ = 1

theorem langRatCentralizerDetectsP_of_big_two (hB : LangRatCentralizerDetectsPBig)
    (hT : LangRatCentralizerDetectsPTwo) : LangRatCentralizerDetectsP := by
  intro τ L _ _ p₀ p f S hτ hp hp2 hpL hq π hπ ε hε hρ hpε hAlg a b ha hb hap hbp i hqs hle γ hγ
  by_cases hf : 2 ≤ f
  · exact hB τ L p₀ p f S hτ hp hp2 hpL hq hf a b ha hb hap hbp i hqs hle γ hγ
  · have hf0 : f ≠ 0 := by
      rintro rfl
      have h := S.hqpow.1
      rw [hq, pow_zero] at h
      exact not_isPrimePow_one h
    have hf1 : f = 1 := by omega
    subst hf1
    exact hT τ L p₀ p S hτ hp hp2 hpL (by simpa using hq) π hπ ε hε hρ hpε hAlg a b ha hb hap hbp i
      hqs hle γ hγ

end Statements

section Big

theorem langRatCentralizerDetectsPBig : LangRatCentralizerDetectsPBig := by
  intro τ L _ _ p₀ p f S hτ hp hp2 hpL hq hf a b ha hb hap hbp i _ hle γ hγ
  have hG2 : τ ≠ .G2 := by rcases hτ with rfl | rfl | rfl | rfl <;> decide
  obtain ⟨hs0, -, -⟩ := outer_componentOrbitLength_spec S ha i
  have hq4 : 4 ≤ S.D.q := by
    rw [hq]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have hQ4 : 4 ≤ S.D.q ^ componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) :=
    hq4.trans (Nat.le_self_pow hs0.ne' _)
  have hcomm : ∀ x ∈ rationalComponent S.ρ S.Γ (rootCharHom a) i,
      Commute (rootDiagUnit τ b) x :=
    fun x hx => (Subgroup.mem_centralizer_singleton_iff.1 (hle hx)).symm
  have hspan := commute_rootSpan_of_commute_component_anyT S hG2 ha i (by omega) hQ4
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
  obtain ⟨k, δ, hδ, rfl⟩ := hγ
  have key : ∀ k : ℕ, rootChar b ((S.ρ : (Fin τ.rank → ℤ) → _)^[k] δ) = 1 ∧
      IsRoot τ ((S.ρ : (Fin τ.rank → ℤ) → _)^[k] δ) := by
    intro k
    induction k with
    | zero => exact ⟨hcomp δ hδ, hδ.1.1⟩
    | succ k ih =>
      rw [Function.iterate_succ_apply']
      exact ⟨by rw [S.frob.rootChar_eq b hb _ ih.2, ih.1, one_pow], (S.frob.isRoot_iff _).2 ih.2⟩
  exact (key k).1

end Big

end CFSG.StandardType.LangRat
