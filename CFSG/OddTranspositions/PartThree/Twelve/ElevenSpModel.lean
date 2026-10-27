module

public import CFSG.ClassicalGroups.Orthogonal.Derived
public import CFSG.GroupTheory.WeirSylow.OrthogonalModels
public import Mathlib.FieldTheory.Perfect
public import CFSG.ClassicalInvolution.Orders.OrthogonalCount
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionModels
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointDataModelWitness
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSemilinearDataCompatibility
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenOrthogonalModel
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis

public section

namespace CFSG.OddTranspositions.PartThree.ElevenSp

open QuadraticMap CFSG.ClassicalGroups.Orthogonal

variable {k : ℕ} {F : Type} [Field F]

abbrev MSpace (k : ℕ) (F : Type) : Type := (F × F) × (Fin k ⊕ Fin k → F)

@[expose] noncomputable def mForm (Q₀ : QuadraticForm F (Fin k ⊕ Fin k → F)) :
    QuadraticForm F (MSpace k F) :=
  (CFSG.GroupTheory.WeirSylow.binForm 1 0).prod Q₀

abbrev MGroup (Q₀ : QuadraticForm F (Fin k ⊕ Fin k → F)) : Type :=
  ↥(TauCeti.QuadraticMap.orthogonalGroup (mForm Q₀))

@[expose] noncomputable def mRefl (Q₀ : QuadraticForm F (Fin k ⊕ Fin k → F)) (X : MSpace k F) :
    MGroup Q₀ :=
  ⟨reflect (mForm Q₀) X, reflect_mem_orthogonalGroup _ X⟩

@[expose] def mClass (Q₀ : QuadraticForm F (Fin k ⊕ Fin k → F)) : Set (MGroup Q₀) :=
  {g | ∃ X : MSpace k F, mForm Q₀ X = 1 ∧ g = mRefl Q₀ X}

@[expose] def mU : MSpace k F := ((1, 0), 0)

@[expose] noncomputable def mLift [Finite F] [CharP F 2]
    (Q₀ : QuadraticForm F (Fin k ⊕ Fin k → F)) (x : Fin k ⊕ Fin k → F) : MSpace k F :=
  (((frobeniusEquiv F 2).symm (1 + Q₀ x), 0), x)

@[expose] noncomputable def mStabForm (Q₀ : QuadraticForm F (Fin k ⊕ Fin k → F)) (Y : MSpace k F) :
    QuadraticForm F (Fin k ⊕ Fin k → F) :=
  Q₀ + QuadraticMap.linMulLin (polarBilin Q₀ ((Y.1.2)⁻¹ • Y.2))
    (polarBilin Q₀ ((Y.1.2)⁻¹ • Y.2))

end CFSG.OddTranspositions.PartThree.ElevenSp

end
