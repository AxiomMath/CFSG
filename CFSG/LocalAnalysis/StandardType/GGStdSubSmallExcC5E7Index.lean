module

public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.ExcCross.E6CartanIndexOne
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwRigidSplit
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerResiduals
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwE6
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwLangConsumers
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.LangFrame
public import CFSG.LieType.Chevalley.OddTrialityCosetInvolutions
public import CFSG.LieType.SeitzGeneration.ExtSeitzReeF4Cyclic
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanDiagOuterE6Adj
public import CFSG.LocalAnalysis.AGLEmbedding.SporadicData
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
public import CFSG.RankThree.PartOne.K133H.G2Plane
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

namespace CFSG.StandardType.SmallExc

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.PartOne.KE
  CFSG.HardMathSupport.Curtis.NaturalModuleCensus.ExcCross
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar

set_option linter.unusedSectionVars false

section Index

theorem relIndex_dvd_one_of_card_two {τ : Tag} (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = 2) :
    ∀ (L : Type) [Field L] [Algebra K L] [IsAlgClosure K L] (Fr : L →+* L),
      (∀ c, Fr c = c ^ Nat.card K) → ∀ (X : Subgroup (ModGL τ L)) [Finite X],
        X ≤ adjointGroup τ L → (∀ x ∈ X, Units.map (entrywiseHom Fr) x = x) →
        ((adjointGroup τ K).map (baseChangeGL (algebraMap K L))).relIndex X ∣ 1 := by
  intro L _ _ _ Fr hFr X _ hXC hXF
  classical
  have : Fintype X := Fintype.ofFinite X
  have hdesc : ∀ x : X, ∃ S : Finset L, ∀ E : Subfield L, (S : Set L) ⊆ E →
      ∃ y ∈ adjointGroup τ E, baseChangeGL E.subtype y = (x : ModGL τ L) :=
    fun x => CFSG.LieType.Chevalley.exists_finset_descent (hXC x.2)
  choose Sx hSx using hdesc
  obtain ⟨E, hEf, hSE, hKE⟩ :=
    exists_finite_subfield_of_finset (K := K) (L := L) (Finset.univ.biUnion Sx)
  have : Finite E := hEf
  have hSE' : ∀ x : X, (Sx x : Set L) ⊆ E := fun x a ha =>
    hSE (Finset.mem_coe.2 (Finset.mem_biUnion.2 ⟨x, Finset.mem_univ _, Finset.mem_coe.1 ha⟩))
  obtain ⟨σE, hσE, hJ, hfix⟩ := exists_subfieldFrobenius_data (τ := τ) Fr hFr E hKE
  have hJn : ((fixedFieldImage τ σE).subgroupOf (entrywiseFixedGroup τ σE)).Normal :=
    fixedFieldImage_normal
  have hidx : ((fixedFieldImage τ σE).subgroupOf (entrywiseFixedGroup τ σE)).index ∣ 1 := by
    have h := CFSG.HardMathSupport.Curtis.NaturalModuleCensus.ExcCross.fixedFieldImage_index_dvd_card_units (τ := τ) σE
    rw [Nat.card_units, natCard_fixSubfield_eq Fr hFr E hKE σE hσE, hK] at h
    simpa using h
  have hιE : Function.Injective (baseChangeGL (τ := τ) E.subtype) :=
    baseChangeGL_injective E.subtype
  set A : Subgroup (ModGL τ E) :=
    X.comap (baseChangeGL E.subtype) ⊓ adjointGroup τ E with hA
  have hXA : X = A.map (baseChangeGL E.subtype) := by
    refine le_antisymm (fun x hx => ?_) ?_
    · obtain ⟨y, hy, hyx⟩ := hSx ⟨x, hx⟩ E (hSE' ⟨x, hx⟩)
      refine ⟨y, ⟨?_, hy⟩, hyx⟩
      have h1 : baseChangeGL E.subtype y = x := hyx
      show baseChangeGL E.subtype y ∈ X
      rw [h1]
      exact hx
    · rintro _ ⟨y, hy, rfl⟩
      exact hy.1
  have hAΓ : A ≤ entrywiseFixedGroup τ σE := fun y hy =>
    hfix y hy.2 (hXF _ hy.1)
  rw [← hJ, hXA, Subgroup.relIndex_map_map_of_injective _ _ hιE]
  have h1 : ((fixedFieldImage τ σE).subgroupOf (entrywiseFixedGroup τ σE)).relIndex
      (A.subgroupOf (entrywiseFixedGroup τ σE)) =
      (fixedFieldImage τ σE).relIndex A := Subgroup.relIndex_subgroupOf hAΓ
  rw [← h1]
  exact (Subgroup.relIndex_dvd_index_of_normal _ _).trans hidx

end Index

end CFSG.StandardType.SmallExc

end
