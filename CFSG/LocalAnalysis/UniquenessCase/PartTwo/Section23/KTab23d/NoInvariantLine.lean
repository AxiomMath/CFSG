module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23d.Defs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23c.OmegaMinusFour
import CFSG.ClassicalGroups.SpecialLinear.Transitive
import CFSG.ClassicalGroups.Orthogonal.StatedOmegaElementary
import CFSG.LieType.Universal.Spin.Forms
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

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.KTabD

open CFSG.Open

theorem lineStab_statedSL_two_ne_top {K : Type} [Field K] {w₀ : Fin 2 → K} (hw₀ : w₀ ≠ 0) :
    lineStab (StatedSL 2 K) w₀ ≠ ⊤ := by
  intro htop
  obtain ⟨y, hy0, hy⟩ : ∃ y : Fin 2 → K, y ≠ 0 ∧ ∀ c : K, y ≠ c • w₀ := by
    by_cases h1 : w₀ 1 = 0
    · refine ⟨Pi.single 1 1, ?_, fun c hc => ?_⟩
      · intro h
        simpa using congrFun h 1
      · have := congrFun hc 1
        simp [h1] at this
    · refine ⟨Pi.single 0 1, ?_, fun c hc => ?_⟩
      · intro h
        simpa using congrFun h 0
      · have e1 := congrFun hc 1
        have e0 := congrFun hc 0
        simp [h1] at e1 e0
        subst e1
        simp at e0
  obtain ⟨A, hA, hAx⟩ :=
    CFSG.ClassicalGroups.SpecialLinear.exists_statedSL_mulVec_eq (m := 2) le_rfl hw₀ hy0
  have hmem : (⟨A, hA⟩ : ↥(StatedSL 2 K)) ∈ lineStab (StatedSL 2 K) w₀ :=
    htop ▸ Subgroup.mem_top _
  obtain ⟨c, hc⟩ := hmem
  exact hy c (hAx.symm.trans hc)

section

open Matrix CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin QuadraticMap

theorem lineStab_statedOmegaMinus_two_ne_top {K : Type} [Field K] [Finite K] [CharP K 2]
    {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    lineStab (StatedOmega (StatedQuadMinus 2 K b c)) (KTabC.e1M K) ≠ ⊤ := by
  intro htop
  let Q := quadMinus 2 K b c
  let u : Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2 → K := Pi.single (Sum.inr (Sum.inl 0)) 1
  let w : Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2 → K := Pi.single (Sum.inr (Sum.inr 0)) 1
  have hu : Q u = 0 := by
    rw [quadMinus_apply]
    simp [u, Pi.single_apply]
  have huw : polar Q u w = 0 := by
    rw [polar_quadMinus]
    simp [u, w, Pi.single_apply]
  let g : Gom Q := ⟨eichler Q u w, eichler_mem_elementaryGroup Q u w⟩
  let A : ↥(StatedOmega (StatedQuadMinus 2 K b c)) := (statedOmegaMinusEquiv le_rfl hirr).symm g
  have hA : ((A : GL (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2) K) : Matrix _ _ K) *ᵥ KTabC.e1M K =
      eichler Q u w (KTabC.e1M K) := by
    change ((statedOmegaMinusEquiv le_rfl hirr).symm g :
      GL (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2) K).val *ᵥ KTabC.e1M K = _
    rw [statedOmegaMinusEquiv_symm_app]
    rfl
  have hmem : A ∈ lineStab (StatedOmega (StatedQuadMinus 2 K b c)) (KTabC.e1M K) :=
    htop ▸ Subgroup.mem_top A
  obtain ⟨c', hc'⟩ := hmem
  have h1 := congrFun hc' (Sum.inr (Sum.inr 0))
  rw [hA, eichler_apply hu huw] at h1
  have e1 : polar Q (KTabC.e1M K) u = 1 := by
    rw [polar_quadMinus]
    simp [u, KTabC.e1M, Pi.single_apply]
  have e2 : polar Q (KTabC.e1M K) w = 0 := by
    rw [polar_quadMinus]
    simp [w, KTabC.e1M, Pi.single_apply]
  have e3 : Q w = 1 := by
    rw [quadMinus_apply]
    simp [w, Pi.single_apply]
  rw [e1, e2, e3] at h1
  simp [KTabC.e1M, u, w, Pi.single_apply] at h1

end

end CFSG.LocalAnalysis.UniquenessCase.UC22.KTabD
