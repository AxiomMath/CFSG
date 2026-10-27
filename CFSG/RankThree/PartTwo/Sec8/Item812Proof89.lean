module

public import CFSG.RankThree.PartTwo.Sec8.Item812ProofFinal
import CFSG.RankThree.PartTwo.KFacts.K71Sp4
import CFSG.RankThree.PartTwo.KFacts.K71Item89
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.GroupTheory.HallHigmanPiCore
public import CFSG.LieType.Chevalley.LangRootArithmetic
public import CFSG.LinearAlgebra.LinearGroups.ProjectiveSimple
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCorePrimeCore
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalDescentEndpoint
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFiveStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFixedTransfer
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionModels
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointPlusBorelModel
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareField
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixComponentsCover
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixModelGeometry
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalTraceZeroCoordinates
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBProjectiveInvolutionStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticBField
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticBLinear
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticRepresentationOdd
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpExclusion
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasFive
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalStandardFormsRegular
public import CFSG.LocalAnalysis.ComponentInitial.SuzukiModelSchreier
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiModelPointStructure
public import CFSG.RankThree.PartTwo.Sec12.Notation
public import CFSG.RankThree.PartTwo.Sec4.Item47Diag
public import CFSG.RankThree.PartTwo.Sec4.Item47Statement
public import CFSG.RankThree.PartTwo.Sec4.Item47Witness
public import CFSG.RankThree.PartTwo.Sec4.LThreePiItem411
public import CFSG.RankThree.PartTwo.Sec4.ProjSLEquiv
public import CFSG.StronglyEmbedded.ParityCriterion
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldFixedSubfieldCard
public import TauCeti.LinearAlgebra.Dimension.IsQuadraticExtension
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup.LowRank

public section

namespace CFSG.RankThree.PartTwo.Sec8

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)

@[expose] def KF89J : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (a b : G)
    (X : Subgroup G) (n : ℕ), Sec8Pair G A c L a b X n →
    ∀ Y ∈ thetaComponentsAt 3 a, sec8I L a ⊔ sec8J X a ≤ Y →
      ¬ (KFacts.InducesStdKind Y c .field ∨ KFacts.InducesStdKind Y c .graphField) ∧
        ¬ (KFacts.InducesStdKind Y b .field ∨ KFacts.InducesStdKind Y b .graphField) →
      (Nonempty (Y ⧸ aschbacherSolvableCore 3 Y ≃* alternatingGroup (Fin 9)) ∨
          Nonempty (Y ⧸ aschbacherSolvableCore 3 Y ≃* projSp 3 (GaloisField 2 1))) ∧
        Nonempty (perfectResidual (barCentralizer (Subgroup.zpowers a) X) ≃*
          alternatingGroup (Fin 6))

@[expose] def KF89GTwo : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X : Subgroup G) (a : G) (q : TauCeti.PrimePower),
    q.p = 2 → IsoGTwo (X ⧸ aschbacherSolvableCore 3 X) q → a ^ 3 = 1 →
    InducesOuterTheta a X →
    ¬ Nonempty (perfectResidual (barCentralizer (Subgroup.zpowers a) X) ≃*
      alternatingGroup (Fin 6))

@[expose] def KF89TrialityD4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X : Subgroup G) (a : G) (q : TauCeti.PrimePower)
    (hq : (TauCeti.LieTypeIndex.trialityD4 q).Valid), q.p = 2 →
    Nonempty (X ⧸ aschbacherSolvableCore 3 X ≃* (TauCeti.CFSGIndex.lie ⟨.trialityD4 q, hq⟩).Group) →
    a ^ 3 = 1 → InducesOuterTheta a X →
    ¬ Nonempty (perfectResidual (barCentralizer (Subgroup.zpowers a) X) ≃*
      alternatingGroup (Fin 6))

@[expose] def KF89ReeF4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X : Subgroup G) (a : G) (k : ℕ)
    (hk : (TauCeti.LieTypeIndex.reeF4 k).Valid),
    Nonempty (X ⧸ aschbacherSolvableCore 3 X ≃* (TauCeti.CFSGIndex.lie ⟨.reeF4 k, hk⟩).Group) →
    a ^ 3 = 1 → InducesOuterTheta a X →
    ¬ Nonempty (perfectResidual (barCentralizer (Subgroup.zpowers a) X) ≃*
      alternatingGroup (Fin 6))

@[expose] def Pair89Omega : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (a b : G)
    (X : Subgroup G) (n : ℕ), Sec8Pair G A c L a b X n →
    ∀ Y ∈ thetaComponentsAt 3 a, sec8I L a ⊔ sec8J X a ≤ Y →
      ¬ (KFacts.InducesStdKind Y c .field ∨ KFacts.InducesStdKind Y c .graphField) ∧
        ¬ (KFacts.InducesStdKind Y b .field ∨ KFacts.InducesStdKind Y b .graphField) →
      Nonempty (X ⧸ aschbacherSolvableCore 3 X ≃* projSp 2 (GaloisField 2 3)) →
      (Nonempty (Y ⧸ aschbacherSolvableCore 3 Y ≃* alternatingGroup (Fin 9)) ∨
          Nonempty (Y ⧸ aschbacherSolvableCore 3 Y ≃* projSp 3 (GaloisField 2 1))) →
      ∀ p ∈ pairOmega A, IsUnitaryTwo (p.2 ⧸ aschbacherSolvableCore 3 p.2) 3 ∨
        Nonempty (p.2 ⧸ aschbacherSolvableCore 3 p.2 ≃* projSp 2 (GaloisField 2 3))

theorem projSp_of_perfectResidual_barCentralizer (hG2 : KF89GTwo) (hD4 : KF89TrialityD4)
    (hRee : KF89ReeF4) {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G}
    {L : Subgroup G} {a b : G} {X : Subgroup G} {n : ℕ} (h : Sec8Pair G A c L a b X n)
    (hout : InducesOuterTheta a X)
    (hJ : Nonempty (perfectResidual (barCentralizer (Subgroup.zpowers a) X) ≃*
      alternatingGroup (Fin 6))) :
    Nonempty (X ⧸ aschbacherSolvableCore 3 X ≃* projSp 2 (GaloisField 2 3)) := by
  have ha3 : a ^ 3 = 1 := h.mem_partTwoF.1.2 a h.a_mem
  obtain ⟨d, m, -, -, hm, hcases⟩ := h.mem_pairOmega.2.2.2.2.2
  rcases hcases with ⟨k, hk, -, he, -⟩ | ⟨hX, -⟩
  · exact absurd hJ (hRee G X a k hk he ha3 hout)
  rcases hX with ⟨q, hq, hq2, -, he⟩ | ⟨q, hq2, -, hG⟩ | hU | hSU | hSp
  · exact absurd hJ (hD4 G X a q hq hq2 he ha3 hout)
  · exact absurd hJ (hG2 G X a q hq2 hG ha3 hout)
  · exact absurd (Or.inl hU) (h.not_unitary (3 * m))
  · exact absurd (Or.inr hSU) (h.not_unitary (3 * m))
  · obtain ⟨-, hC⟩ := KFacts.barCentralizer_mulEquiv_projSp (by omega) ha3 hout hSp
    have hm1 : m = 1 :=
      KFacts.eq_one_of_perfectResidual_mulEquiv_alternatingGroup_six_of_projSp hm hC hJ
    subst hm1
    simpa using hSp

end CFSG.RankThree.PartTwo.Sec8
