module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23d.Defs
public import CFSG.Open.StatedDefs
public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockOrthMinusCuts
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalTailModelCoordinates

import CFSG.LocalAnalysis.ComponentInitial.OrthogonalTailModelTransport
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointPlusBorelBasic
import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockOrthMinusResGroup
import CFSG.ClassicalGroups.Orthogonal.StatedOmegaElementary
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasFive
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalStandardFormsRegular
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalTailPolar
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalTailWeylLift
import CFSG.CharacterTheory.Semidihedral.DihedralQuaternion
import CFSG.ClassicalGroups.Orthogonal.RootGroupFixedCard
import CFSG.GroupTheory.LocalCores.Fitting
import CFSG.LieType.Steinberg.Classical.SpinFrame
import CFSG.LieType.Steinberg.Exceptional.E6E7
import CFSG.LieType.Steinberg.Families
import CFSG.LieType.Steinberg.G2
import CFSG.LieType.Universal.Spin.Generation
import CFSG.LieType.Universal.Spin.OddCT
import CFSG.LieType.Universal.Spin.PlusCT
import CFSG.LieType.Universal.Spin.Structure
import CFSG.LieType.Universal.SpinOmega
import CFSG.LieType.Universal.Unitary
import CFSG.LinearAlgebra.LinearGroups.ProjectiveSimple
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionModels
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointDataModelWitness
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSemilinearDataCompatibility
import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenOrthogonalModel
import CFSG.LocalAnalysis.SectionRank.ClassicalOdd
import CFSG.LocalAnalysis.SectionRank.EvenCover.LinearStep
import CFSG.LocalAnalysis.SectionRank.SporadicCover
import CFSG.Sporadic.M23.M23Group
import CFSG.Sporadic.Th.F2Spec
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.ComplementTransfer
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
import TauCeti.LinearAlgebra.CliffordAlgebra.Monomials
import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.KTabD

open CFSG.Open
open CFSG.AGLEmbedding.LeviBlock
open CFSG.ClassicalGroups.Orthogonal
open CFSG.ComponentClassification.CatalogueBOrthogonalPointPlusBorel
open CFSG.LieType.Universal.Spin
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail
open scoped Pointwise

private lemma pi_single_inl_ne_zero_Q16 {K : Type} [Field K] (k : ℕ) :
    (Pi.single (Sum.inl (⟨0, by omega⟩ : Fin ((k + 3) - 1))) (1 : K) :
      Fin ((k + 3) - 1) ⊕ Fin ((k + 3) - 1) ⊕ Fin 2 → K) ≠ 0 := by
  intro h
  have h1 : (1 : K) = 0 := by
    simpa using congrFun h (Sum.inl (⟨0, by omega⟩ : Fin ((k + 3) - 1)))
  exact one_ne_zero h1

private lemma map_span_singleton_iff_Q16 {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    (e : V ≃ₗ[K] V) {v : V} (hv : v ≠ 0) :
    (Submodule.span K {v}).map e.toLinearMap = Submodule.span K {v} ↔
      ∃ c : K, e v = c • v := by
  rw [Submodule.map_span, Set.image_singleton]
  change Submodule.span K {e v} = Submodule.span K {v} ↔ ∃ c : K, e v = c • v
  have hev : e v ≠ 0 := fun h => hv (e.injective (by rw [h, map_zero]))
  constructor
  · intro h
    have hmem : e v ∈ Submodule.span K {v} := by
      rw [← h]
      exact Submodule.mem_span_singleton_self (e v)
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
    exact ⟨c, hc.symm⟩
  · rintro ⟨c, hc⟩
    have hc0 : c ≠ 0 := fun hcz => hev (by rw [hc, hcz, zero_smul])
    rw [hc]
    exact Submodule.span_singleton_smul_eq (IsUnit.mk0 c hc0) v

private lemma lineStab_statedQuadMinus_eq_span_Q16 {K : Type} [Field K] {b c : K} (k : ℕ)
    (w : Fin ((k + 3) - 1) ⊕ Fin ((k + 3) - 1) ⊕ Fin 2 → K) :
    lineStab (StatedOmega (StatedQuadMinus (k + 3) K b c)) w =
      statedDerivedSubspaceStabilizer (StatedQuadMinus (k + 3) K b c)
        (Submodule.span K {w}) := by
  ext γ
  by_cases hw : w = 0
  · subst hw
    rw [mem_lineStab, mem_statedDerivedSubspaceStabilizer, Submodule.span_zero_singleton,
      Submodule.map_bot]
    simp
  · rw [mem_lineStab, mem_statedDerivedSubspaceStabilizer,
      map_span_singleton_iff_Q16 (toLinEquiv _ K γ.val) hw]
    simp only [toLinEquiv_apply]

private lemma minusTailIsometry_hypVec_inl_Q16 {K : Type} [Field K] {b c : K} (k : ℕ)
    (i : Fin (k + 2)) :
    (minusTailIsometry (k + 3) K b c) (hypVec K (Fin 2 → K) (Sum.inl i)) =
      (Pi.single (Sum.inl i) 1 : Fin (k + 2) ⊕ Fin (k + 2) ⊕ Fin 2 → K) := by
  change tailModelEquiv (k + 2) K (Fin 2) (hypVec K (Fin 2 → K) (Sum.inl i)) =
    (Pi.single (Sum.inl i) 1 : Fin (k + 2) ⊕ Fin (k + 2) ⊕ Fin 2 → K)
  exact tailModelEquiv_hypVec_inl i

private lemma span_symm_eq_tailFlag_Q16 {K : Type} [Field K] {b c : K} (k : ℕ) :
    (Submodule.span K {(Pi.single (Sum.inl (⟨0, by omega⟩ : Fin ((k + 3) - 1))) (1 : K) :
        Fin ((k + 3) - 1) ⊕ Fin ((k + 3) - 1) ⊕ Fin 2 → K)}).map
      (minusTailIsometry (k + 3) K b c).symm.toLinearMap =
      tailFlag K (Fin 2 → K) (k + 2) 1 := by
  have hsymm : (minusTailIsometry (k + 3) K b c).symm
        (Pi.single (Sum.inl (⟨0, by omega⟩ : Fin ((k + 3) - 1))) (1 : K) :
          Fin ((k + 3) - 1) ⊕ Fin ((k + 3) - 1) ⊕ Fin 2 → K) =
        hypVec K (Fin 2 → K) (Sum.inl (0 : Fin (k + 2))) := by
    rw [QuadraticMap.IsometryEquiv.symm_apply_eq]
    exact (minusTailIsometry_hypVec_inl_Q16 (k := k) 0).symm
  rw [Submodule.map_span, Set.image_singleton]
  let y : (Fin ((k + 3) - 1) ⊕ Fin ((k + 3) - 1) → K) × (Fin 2 → K) :=
    (minusTailIsometry (k + 3) K b c).symm
      (Pi.single (Sum.inl (⟨0, by omega⟩ : Fin ((k + 3) - 1))) (1 : K) :
        Fin ((k + 3) - 1) ⊕ Fin ((k + 3) - 1) ⊕ Fin 2 → K)
  change Submodule.span K {y} = tailFlag K (Fin 2 → K) (k + 2) 1
  rw [show y = hypVec K (Fin 2 → K) (Sum.inl (0 : Fin (k + 2))) from hsymm, tailFlag]
  congr 1
  ext v
  simp only [Set.mem_image, Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · intro hv
    exact ⟨0, by simp, hv.symm⟩
  · rintro ⟨j, hj, rfl⟩
    have hjval : (j : ℕ) = 0 := Nat.lt_one_iff.mp hj
    have hj0 : j = 0 := Fin.ext (by simpa using hjval)
    subst hj0
    rfl

private lemma stabilizer_tailFlag_one_eq_orthParab_Q16 {K : Type} [Field K] {A : Type}
    [AddCommGroup A] [Module K A] {r : ℕ} (qA : QuadraticForm K A) :
    MulAction.stabilizer (orthElementaryGroup (quadTail r qA)) (tailFlag K A r 1) =
      orthParab r qA ![0, 1] := by
  ext x
  rw [mem_stabilizer_iff_map (Q := quadTail r qA), mem_orthParab, Fin.forall_fin_two]
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · simp only [Matrix.cons_val_zero, tailFlag_zero, Submodule.map_bot]
    · simpa using h
  · rintro ⟨-, h1⟩
    simpa using h1

theorem exists_mulEquiv_lineStab_map_eq_orthParab {K : Type} [Field K] [Finite K] [CharP K 2]
    {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (k : ℕ) :
    ∃ φ : ↥(StatedOmega (StatedQuadMinus (k + 3) K b c)) ≃*
        ↥(orthElementaryGroup (quadTail (k + 2) (minusTailForm K b c))),
      (lineStab (StatedOmega (StatedQuadMinus (k + 3) K b c))
        (Pi.single (Sum.inl ⟨0, by omega⟩) 1)).map φ.toMonoidHom =
          orthParab (k + 2) (minusTailForm K b c) ![0, 1] := by
  have hQ : ⇑(quadMinus (k + 3) K b c) = StatedQuadMinus (k + 3) K b c :=
    coe_quadMinus (k + 3) K b c
  have hE : ⁅TauCeti.QuadraticMap.orthogonalGroup (quadMinus (k + 3) K b c),
      TauCeti.QuadraticMap.orthogonalGroup (quadMinus (k + 3) K b c)⁆ =
      elementaryGroup (quadMinus (k + 3) K b c) :=
    commutator_orthogonalGroup_quadMinus_of_two_le (n := k + 3) (by omega) hirr
  refine ⟨tailOmegaEquiv (minusTailIsometry (k + 3) K b c) hQ hE, ?_⟩
  rw [lineStab_statedQuadMinus_eq_span_Q16 (k := k),
    tailOmegaEquiv_subspaceStabilizer (minusTailIsometry (k + 3) K b c) hQ hE,
    span_symm_eq_tailFlag_Q16 (k := k)]
  exact stabilizer_tailFlag_one_eq_orthParab_Q16 (minusTailForm K b c)

end CFSG.LocalAnalysis.UniquenessCase.UC22.KTabD
