module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S172CCentFrame
public import CFSG.RankThree.PartOne.KC.OrthogonalBlockDet
public import CFSG.ClassicalGroups.Orthogonal.Eichler
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
public import CFSG.RankThree.PartOne.KC.OrthogonalFixedDerived
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.StandardType.OmNsRootGen

open Polynomial QuadraticMap CFSG.RankThree.Classical2 CFSG.RankThree.PartOne.KCOrthogonal
  CFSG.LocalAnalysis.GLTheoremA.S172C.Cent

variable {F : Type} [Field F] [Finite F] {V : Type} [AddCommGroup V] [Module F V]

@[expose] noncomputable def framePoly (t : F) : F[X] := X ^ 2 + C t * X + 1

structure IsCoherentFrame (Q : QuadraticForm F V) (p : ℕ) {k : ℕ} (U : Fin k → Submodule F V)
    (e : Fin k → ↥(orthDerived Q)) (E : Subgroup ↥(orthDerived Q)) (u : Fin k → V) (c t : F) :
    Prop extends IsPlaneFrame Q p U e E where
  mem : ∀ a, u a ∈ U a
  quad_eq : ∀ a, Q (u a) = c
  c_ne_zero : c ≠ 0
  t_ne_zero : t ≠ 0
  rot : ∀ a, (e a : V ≃ₗ[F] V) ((e a : V ≃ₗ[F] V) (u a)) = t • (e a : V ≃ₗ[F] V) (u a) + u a
  polar_eq : ∀ a, polar Q (u a) ((e a : V ≃ₗ[F] V) (u a)) = t * c

variable {k : ℕ}

@[expose] noncomputable def frameSwap (Q : QuadraticForm F V) (e : Fin k → ↥(orthDerived Q))
    (u : Fin k → V) (c t : F) (a b : Fin k) : V ≃ₗ[F] V :=
  CFSG.ClassicalGroups.Orthogonal.eichler Q (u a + u b)
    ((t * c)⁻¹ • ((e a : V ≃ₗ[F] V) (u a) + (e b : V ≃ₗ[F] V) (u b)))

@[expose] noncomputable def pairBlock (Q : QuadraticForm F V) (e : Fin k → ↥(orthDerived Q))
    (t : F) (a b : Fin k) (s : Bool) : Subgroup ↥(orthDerived Q) :=
  (specialBlock Q ((e a * cond s (e b)⁻¹ (e b) : ↥(orthDerived Q)) : V ≃ₗ[F] V)
    (framePoly t)).subgroupOf (orthDerived Q)

end CFSG.StandardType.OmNsRootGen

end
