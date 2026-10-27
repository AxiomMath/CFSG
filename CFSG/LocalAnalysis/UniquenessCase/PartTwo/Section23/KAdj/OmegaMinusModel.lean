module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23d.Defs
public import CFSG.Open.StatedDefs
public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockOrthMinusCuts
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalTailModelCoordinates
import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockOrthMinusData
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasFive
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalStandardFormsRegular
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalTailPolar
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalTailWeylLift
import CFSG.Foundations
import CFSG.LinearAlgebra.LinearGroups.ProjectiveSimple
import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeFamilies
import CFSG.LocalAnalysis.AGLEmbedding.D1GlobalU
import CFSG.LocalAnalysis.AGLEmbedding.IIIaResidualDefs
import CFSG.LocalAnalysis.AGLEmbedding.J3MSideDefs
import CFSG.LocalAnalysis.AGLEmbedding.JStarReducedDefs
import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockOrthMinusBlocks
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionModels
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointDataModelWitness
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSemilinearDataCompatibility
import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierAlternatingSix
import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
import CFSG.LocalAnalysis.ComponentInitial.LinearHigherBorelOvergroups
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalTailModelBorel
import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenOrthogonalModel
import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Reduce
import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeBasic
import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
import CFSG.Quasithin.Background.A1cModuleCoprime
import CFSG.Quasithin.Background.A3Components
import CFSG.Quasithin.Background.A3Structure312
import CFSG.Quasithin.Background.OrderingMax
import CFSG.Quasithin.Vol2.Ch1Local
import CFSG.Sporadic.J4Base
import Certificates.Certificate8026Base
import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.KAdjE

open CFSG.Open CFSG.AGLEmbedding.LeviBlock CFSG.ClassicalGroups.Orthogonal
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail
open CFSG.LocalAnalysis.UniquenessCase.UC22.KTabD (lineStab)

abbrev OmegaMinusE (K : Type) [Field K] (b c : K) : Type :=
  ↥(orthElementaryGroup (quadTail 3 (minusTailForm K b c)))

noncomputable abbrev omegaMinusTailQZero (K : Type) [Field K] (b c : K) :
    Subgroup (OmegaMinusE K b c) :=
  orthParab 3 (minusTailForm K b c) ![0, 1]

noncomputable abbrev omegaMinusTailQAlpha (K : Type) [Field K] (b c : K) :
    Subgroup (OmegaMinusE K b c) :=
  orthParab 3 (minusTailForm K b c) ![0, 2, 3]

abbrev omegaMinusQZero (K : Type) [Field K] (b c : K) :
    Subgroup ↥(StatedOmega (StatedQuadMinus 4 K b c)) :=
  lineStab (StatedOmega (StatedQuadMinus 4 K b c)) (Pi.single (Sum.inl ⟨0, by omega⟩) 1)

instance omegaMinusE_finite (K : Type) [Field K] [Finite K] (b c : K) :
    Finite (OmegaMinusE K b c) := by
  haveI : Finite (((Fin 3 ⊕ Fin 3 → K) × (Fin 2 → K)) ≃ₗ[K]
      ((Fin 3 ⊕ Fin 3 → K) × (Fin 2 → K))) := finite_orthLinearEquiv
  infer_instance

private theorem mem_tailQZero_iff_E12 {K : Type} [Field K] {b c : K} (x : OmegaMinusE K b c) :
    x ∈ omegaMinusTailQZero K b c ↔
      (tailFlag K (Fin 2 → K) 3 1).map (((x : OmegaMinusE K b c) :
        ((Fin 3 ⊕ Fin 3 → K) × (Fin 2 → K)) ≃ₗ[K] ((Fin 3 ⊕ Fin 3 → K) × (Fin 2 → K))) :
        ((Fin 3 ⊕ Fin 3 → K) × (Fin 2 → K)) →ₗ[K] ((Fin 3 ⊕ Fin 3 → K) × (Fin 2 → K))) =
        tailFlag K (Fin 2 → K) 3 1 := by
  rw [omegaMinusTailQZero, mem_orthParab]
  constructor
  · intro h
    simpa using h 1
  · intro h j
    fin_cases j
    · simp [tailFlag_zero]
    · simpa using h

private theorem mem_tailQAlpha_iff_E12 {K : Type} [Field K] {b c : K} (x : OmegaMinusE K b c) :
    x ∈ omegaMinusTailQAlpha K b c ↔
      (∀ i ∈ ({2, 3} : Finset ℕ), (tailFlag K (Fin 2 → K) 3 i).map (((x : OmegaMinusE K b c) :
        ((Fin 3 ⊕ Fin 3 → K) × (Fin 2 → K)) ≃ₗ[K] ((Fin 3 ⊕ Fin 3 → K) × (Fin 2 → K))) :
        ((Fin 3 ⊕ Fin 3 → K) × (Fin 2 → K)) →ₗ[K] ((Fin 3 ⊕ Fin 3 → K) × (Fin 2 → K))) =
        tailFlag K (Fin 2 → K) 3 i) := by
  rw [omegaMinusTailQAlpha, mem_orthParab]
  constructor
  · intro h i hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl
    · simpa using h 1
    · simpa using h 2
  · intro h j
    fin_cases j
    · simp [tailFlag_zero]
    · simpa using h 2 (by simp)
    · simpa using h 3 (by simp)

theorem omegaMinusTailQZero_inf_QAlpha (K : Type) [Field K] (b c : K) :
    omegaMinusTailQZero K b c ⊓ omegaMinusTailQAlpha K b c =
      (tailBorel 3 (minusTailForm K b c)).subgroupOf
        (orthElementaryGroup (quadTail 3 (minusTailForm K b c))) := by
  ext x
  rw [Subgroup.mem_inf, mem_tailQZero_iff_E12, mem_tailQAlpha_iff_E12,
    Subgroup.mem_subgroupOf, mem_tailBorel]
  constructor
  · rintro ⟨h1, h23⟩
    refine ⟨by simpa using x.2, fun i hi1 hi3 => ?_⟩
    rcases (show i = 1 ∨ i = 2 ∨ i = 3 by omega) with rfl | rfl | rfl
    · exact h1
    · exact h23 2 (by simp)
    · exact h23 3 (by simp)
  · rintro ⟨-, h⟩
    refine ⟨h 1 le_rfl (by norm_num), fun i hi => ?_⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl
    · exact h 2 (by norm_num) (by norm_num)
    · exact h 3 (by norm_num) (by norm_num)

end CFSG.LocalAnalysis.UniquenessCase.UC22.KAdjE
