module

public import CFSG.Open.StatedDefs
import CFSG.ClassicalGroups.Orthogonal.StatedOmegaElementary
import CFSG.ClassicalGroups.Orthogonal.RootGroupStabilizer
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23a.RootFix
import CFSG.CharacterTheory.Semidihedral.DihedralQuaternion
import CFSG.ClassicalGroups.Orthogonal.RootGroupFixedCard
import CFSG.GroupTheory.LocalCores.Fitting
import CFSG.LinearAlgebra.LinearGroups.ProjectiveSimple
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionModels
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointDataModelWitness
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSemilinearDataCompatibility
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenOrthogonalModel
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.ComplementTransfer
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.KTabA

open CFSG.Open
open CFSG.ClassicalGroups.Orthogonal
open CFSG.LieType.Universal.Spin
open QuadraticMap
open scoped Matrix

private lemma quadMinus_single_inl_apply {K : Type} [Field K] {m : ℕ} (j : Fin (m - 1))
    (b c : K) :
    quadMinus m K b c (Pi.single (Sum.inl j) (1 : K) :
      Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2 → K) = 0 := by
  rw [quadMinus_apply]
  simp [Pi.single_apply]

private lemma pi_single_inl_ne_zero {K : Type} [Field K] {m : ℕ} (j : Fin (m - 1)) :
    (Pi.single (Sum.inl j) (1 : K) : Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2 → K) ≠ 0 := by
  intro h
  have h1 : (1 : K) = 0 := by simpa [Pi.single_apply] using congrFun h (Sum.inl j)
  exact one_ne_zero h1

private lemma isPGroup_lomGLMinus_subgroupOf {K : Type} [Field K] [Finite K] [CharP K 2] {m : ℕ}
    (hm : 2 ≤ m) {b c : K} (hbc : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (u : Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2 → K) :
    IsPGroup 2 ((LomGLMinus hm hbc u).subgroupOf (StatedOmega (StatedQuadMinus m K b c))) := by
  have h1 : IsPGroup 2 ((Lom (quadMinus m K b c) u).map
      (statedOmegaMinusEquiv hm hbc).symm.toMonoidHom) :=
    (isPGroup_Lom (Q := quadMinus m K b c) u).map _
  have h2 : IsPGroup 2 (((Lom (quadMinus m K b c) u).map
      (statedOmegaMinusEquiv hm hbc).symm.toMonoidHom).map
      (StatedOmega (StatedQuadMinus m K b c)).subtype) := h1.map _
  rw [LomGLMinus]
  exact h2.comap_subtype

private lemma mem_lomGLMinus_subgroupOf_symm {K : Type} [Field K] [Finite K] [CharP K 2] {m : ℕ}
    (hm : 2 ≤ m) {b c : K} (hbc : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    {u : Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2 → K} {g : Gom (quadMinus m K b c)}
    (hg : g ∈ Lom (quadMinus m K b c) u) :
    ((statedOmegaMinusEquiv hm hbc).symm g : ↥(StatedOmega (StatedQuadMinus m K b c))) ∈
      (LomGLMinus hm hbc u).subgroupOf (StatedOmega (StatedQuadMinus m K b c)) := by
  refine Subgroup.mem_subgroupOf.mpr ?_
  rw [LomGLMinus]
  exact Subgroup.mem_map.mpr ⟨(statedOmegaMinusEquiv hm hbc).symm g,
    Subgroup.mem_map.mpr ⟨g, hg, rfl⟩, rfl⟩

theorem exists_fixedLine_statedOmega_minus_single {K : Type} [Field K] [Finite K] [CharP K 2]
    {m : ℕ} (hm : 2 ≤ m) {b c : K}
    (hbc : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    ∃ U : Subgroup ↥(StatedOmega (StatedQuadMinus m K b c)), IsPGroup 2 ↥U ∧
      ∀ v : Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2 → K,
        (∀ u ∈ U, ((u : GL (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) K) : Matrix _ _ K) *ᵥ v = v) →
          v ∈ Submodule.span K
            {(Pi.single (Sum.inl ⟨0, by omega⟩) 1 : Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2 → K)} := by
  have hm0 : 0 < m - 1 := by omega
  let u : Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2 → K := Pi.single (Sum.inl ⟨0, hm0⟩) 1
  refine ⟨(LomGLMinus hm hbc u).subgroupOf (StatedOmega (StatedQuadMinus m K b c)), ?_, ?_⟩
  · exact isPGroup_lomGLMinus_subgroupOf hm hbc u
  · intro v hv
    refine mem_span_of_forall_eichler_apply_eq (Q := quadMinus m K b c)
      (nondegenerate_polarBilin_quadMinus_of_finite m K hbc) ?_ ?_ ?_ ?_
    · rw [Module.finrank_fintype_fun_eq_card]
      simp only [Fintype.card_sum, Fintype.card_fin]
      omega
    · exact quadMinus_single_inl_apply ⟨0, hm0⟩ b c
    · exact pi_single_inl_ne_zero ⟨0, hm0⟩
    · intro w hw
      let g : Gom (quadMinus m K b c) :=
        ⟨eichler (quadMinus m K b c) u w,
          eichler_mem_elementaryGroup (quadMinus m K b c) u w⟩
      have hg : g ∈ Lom (quadMinus m K b c) u := by
        exact eichler_mem_rootGroup (Q := quadMinus m K b c) hw
      let A : ↥(StatedOmega (StatedQuadMinus m K b c)) := (statedOmegaMinusEquiv hm hbc).symm g
      have hA : A ∈ (LomGLMinus hm hbc u).subgroupOf (StatedOmega (StatedQuadMinus m K b c)) :=
        mem_lomGLMinus_subgroupOf_symm hm hbc hg
      have hfixA := hv A hA
      have h1 : (((A : GL (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) K)) : Matrix _ _ K) *ᵥ v =
          eichler (quadMinus m K b c) u w v := by
        change ((statedOmegaMinusEquiv hm hbc).symm g :
          GL (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) K).val *ᵥ v =
          eichler (quadMinus m K b c) u w v
        rw [statedOmegaMinusEquiv_symm_app]
        rfl
      rw [h1] at hfixA
      exact hfixA

theorem exists_fixedLine_statedOmega_minus {K : Type} [Field K] [Finite K] [CharP K 2] {m : ℕ}
    (hm : 2 ≤ m) {b c : K}
    (hbc : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    ∃ (U : Subgroup ↥(StatedOmega (StatedQuadMinus m K b c)))
      (e : Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2 → K), IsPGroup 2 ↥U ∧
      ∀ v : Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2 → K,
        (∀ u ∈ U, ((u : GL (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) K) : Matrix _ _ K) *ᵥ v = v) →
          v ∈ Submodule.span K {e} :=
  let ⟨U, hU, hfix⟩ := exists_fixedLine_statedOmega_minus_single hm hbc
  ⟨U, _, hU, hfix⟩

end CFSG.LocalAnalysis.UniquenessCase.UC22.KTabA
