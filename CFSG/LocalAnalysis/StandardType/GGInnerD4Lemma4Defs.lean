module

public import CFSG.Foundations.Basic
public import CFSG.LocalAnalysis.StandardType.GGNbrTableForms
public import CFSG.RankThree.PartOne.KC.OrthogonalFixedDerived
public import CFSG.GroupTheory.WeirSylow.OrthogonalModels
public import CFSG.Open.Defs
public import CFSG.ClassicalInvolution.Orders.OrthogonalCount
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionModels
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointDataModelWitness
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSemilinearDataCompatibility
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenOrthogonalModel
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.RankThree.PartOne.KC.OrthogonalBinaryDickson
public import CFSG.RankThree.PartOne.KC.OrthogonalBlockProduct
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis

public section

namespace CFSG.StandardType.S2MathAs51586Freeze

open Polynomial Module
open CFSG.Assembly CFSG.RankThree.Classical2 CFSG.RankThree.PartOne.KCPrimary
  CFSG.RankThree.PartOne.KCOrthogonal CFSG.ClassicalGroups.Orthogonal

@[expose] def NonfixedNotD4 : Prop :=
  GGLabelRigidInput → ∀ (K V : Type) [Field K] [Finite K] [CharP K 2]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] (n n' : ℕ),
    1 ≤ n → 1 ≤ n' → Nat.card K = 2 ^ n →
    ∀ (Q : QuadraticForm K V) (x : ↥(orthDerived Q)),
      OddOrderIsometry Q 3 (x : V ≃ₗ[K] V) →
      ∀ (h : K[X]), h ∈ primaryFactors (x : V ≃ₗ[K] V).toLinearMap → h ≠ X - 1 →
        CFSG.IsQuasisimple ↥(specialBlock Q (x : V ≃ₗ[K] V) h) →
        ¬ GGHasLabel (⟨.D, 4, n'⟩ : LargeEvenLabel)
          (componentImage Q (x : V ≃ₗ[K] V) h ⧸
            Subgroup.center (componentImage Q (x : V ≃ₗ[K] V) h))

@[expose] def FixedD4Shape : Prop :=
  GGLabelRigidInput → ∀ (K V : Type) [Field K] [Finite K] [CharP K 2]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] (n n' : ℕ),
    1 ≤ n → 1 ≤ n' → Nat.card K = 2 ^ n →
    ∀ (Q : QuadraticForm K V), (QuadraticMap.polarBilin Q).Nondegenerate →
    ∀ (x : ↥(orthDerived Q)), OddOrderIsometry Q 3 (x : V ≃ₗ[K] V) →
    ∀ (F : Subgroup (V ≃ₗ[K] V)), CFSG.IsQuasisimple ↥F →
      F ≤ supportedFixedDerived Q (x : V ≃ₗ[K] V) →
      (F.subgroupOf (supportedFixedDerived Q (x : V ≃ₗ[K] V))).Normal →
    ∀ (L : Subgroup (ProjOrthDerived Q)),
      L = (F.subgroupOf (orthDerived Q)).map
        (QuotientGroup.mk' ((scalars K V).subgroupOf (orthDerived Q))) →
      GGHasLabel (⟨.D, 4, n'⟩ : LargeEvenLabel) (L ⧸ Subgroup.center L) →
      n' = n ∧ Module.finrank K (fixedSpace (x : V ≃ₗ[K] V)) = 8 ∧
        CFSG.GroupTheory.WeirSylow.IsPlusType
          (Q.comp (fixedSpace (x : V ≃ₗ[K] V)).subtype) ∧
        F = supportedFixedDerived Q (x : V ≃ₗ[K] V)

@[expose] def ComponentD4Identification : Prop :=
  GGLabelRigidInput → ∀ (K V : Type) [Field K] [Finite K] [CharP K 2]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] (n n' : ℕ),
    1 ≤ n → 1 ≤ n' → Nat.card K = 2 ^ n →
    ∀ (Q : QuadraticForm K V), (QuadraticMap.polarBilin Q).Nondegenerate →
    (∃ U : Submodule K V, Module.finrank K U = 3 ∧ ∀ u ∈ U, Q u = 0) →
    ∀ (x : ↥(orthDerived Q)), OddOrderIsometry Q 3 (x : V ≃ₗ[K] V) →
    ∀ (J : Subgroup (ProjOrthDerived Q)),
      CFSG.Open.IsComponentOf J (centralizerImage Q (x : V ≃ₗ[K] V)) →
      GGHasLabel (⟨.D, 4, n'⟩ : LargeEvenLabel) (J ⧸ Subgroup.center J) →
      n' = n ∧ Module.finrank K (fixedSpace (x : V ≃ₗ[K] V)) = 8 ∧
        CFSG.GroupTheory.WeirSylow.IsPlusType
          (Q.comp (fixedSpace (x : V ≃ₗ[K] V)).subtype) ∧
        J = fixedComponentImage Q (x : V ≃ₗ[K] V)

end CFSG.StandardType.S2MathAs51586Freeze
