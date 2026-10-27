module

public import CFSG.Open.StatedDefs
import CFSG.ClassicalGroups.Orthogonal.StatedOmegaElementary
import CFSG.ClassicalGroups.Orthogonal.Omega7ThreeLocalRoot
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
open scoped Matrix
open CFSG.ClassicalGroups.Orthogonal QuadraticMap
open CFSG.LieType.Universal.Spin

private theorem eichler_pow_char {K : Type} [Field K] {m : ℕ} (p : ℕ) [CharP K p]
    (u w : Fin m ⊕ Fin m → K) : eichler (quadPlus m K) u w ^ p = 1 := by
  rw [← ringChar.eq (R := K) p]
  exact CFSG.ClassicalGroups.Orthogonal.Omega7ThreeLocal.eichler_pow_ringChar
    (quadPlus m K) u w

private theorem isPGroup_lomGLPlus_subgroupOf {K : Type} [Field K] (p : ℕ) [CharP K p]
    {m : ℕ} (hm : 3 ≤ m) (u : Fin m ⊕ Fin m → K) :
    IsPGroup p ↥((LomGLPlus hm u).subgroupOf (StatedOmega (StatedQuadPlus m K))) := by
  intro g
  have hmem : ((g : ↥(StatedOmega (StatedQuadPlus m K))) : GL (Fin m ⊕ Fin m) K) ∈
      LomGLPlus hm u := g.2
  obtain ⟨a, ha, haA⟩ := Subgroup.mem_map.mp hmem
  obtain ⟨g₀, hg₀, hfg⟩ := Subgroup.mem_map.mp ha
  obtain ⟨w, hw, hgw⟩ := mem_rootGroup.mp (mem_Lom.mp hg₀)
  have hg₀eq : g₀ = ⟨eichler (quadPlus m K) u w,
      eichler_mem_elementaryGroup (quadPlus m K) u w⟩ := Subtype.ext hgw.symm
  have hg₀pow : g₀ ^ p = 1 := by
    rw [hg₀eq]
    refine Subtype.ext ?_
    simpa using eichler_pow_char (m := m) p u w
  have ha_pow : a ^ p = 1 := by
    rw [← hfg, ← map_pow, hg₀pow, map_one]
  have hga : a = (g : ↥(StatedOmega (StatedQuadPlus m K))) := Subtype.ext haA
  refine ⟨1, ?_⟩
  have hgp : g ^ p = 1 := by
    refine Subtype.ext ?_
    rw [Subgroup.coe_pow, Subgroup.coe_one, ← hga, ha_pow]
  simpa using hgp

theorem exists_fixedLine_statedOmega_plus {K : Type} [Field K] [Finite K] (p : ℕ)
    [Fact p.Prime] [CharP K p] {m : ℕ} (hm : 3 ≤ m) :
    ∃ (U : Subgroup ↥(StatedOmega (StatedQuadPlus m K))) (e : Fin m ⊕ Fin m → K),
      IsPGroup p ↥U ∧
      ∀ v : Fin m ⊕ Fin m → K,
        (∀ u ∈ U, ((u : GL (Fin m ⊕ Fin m) K) : Matrix _ _ K) *ᵥ v = v) →
          v ∈ Submodule.span K {e} := by
  let i0 : Fin m := ⟨0, by omega⟩
  let e : Fin m ⊕ Fin m → K := Pi.single (Sum.inl i0) 1
  have he0 : e ≠ 0 := by
    intro h
    have h1 : (1 : K) = 0 := by simpa [e] using congr_fun h (Sum.inl i0)
    exact one_ne_zero h1
  have heq : quadPlus m K e = 0 := by
    rw [quadPlus_apply]
    simp [e, Pi.single_apply]
  have hd : 3 ≤ Module.finrank K (Fin m ⊕ Fin m → K) := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]
    omega
  refine ⟨(LomGLPlus hm e).subgroupOf (StatedOmega (StatedQuadPlus m K)), e,
    isPGroup_lomGLPlus_subgroupOf p hm e, ?_⟩
  intro v hv
  refine mem_span_of_forall_eichler_apply_eq (nondegenerate_polarBilin_quadPlus m K) hd heq he0 ?_
  intro w hw
  let g₀ : Gom (quadPlus m K) :=
    ⟨eichler (quadPlus m K) e w, eichler_mem_elementaryGroup (quadPlus m K) e w⟩
  have hg₀ : g₀ ∈ Lom (quadPlus m K) e := mem_Lom.mpr (eichler_mem_rootGroup hw)
  let A : ↥(StatedOmega (StatedQuadPlus m K)) := (statedOmegaPlusEquiv hm).symm g₀
  have hA : (A : GL (Fin m ⊕ Fin m) K) ∈ LomGLPlus hm e :=
    Subgroup.mem_map.mpr ⟨A, Subgroup.mem_map.mpr ⟨g₀, hg₀, rfl⟩, rfl⟩
  have hAU : A ∈ (LomGLPlus hm e).subgroupOf (StatedOmega (StatedQuadPlus m K)) := hA
  have h1 : ((A : GL (Fin m ⊕ Fin m) K) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ v
      = g₀.app v := by
    simpa using statedOmegaPlusEquiv_symm_app hm g₀ v
  have h2 := hv A hAU
  rw [h1] at h2
  simpa [Gom.app] using h2

theorem exists_fixedLine_statedOmega_plus_single {K : Type} [Field K] [Finite K] (p : ℕ)
    [Fact p.Prime] [CharP K p] {m : ℕ} (hm : 3 ≤ m) :
    ∃ U : Subgroup ↥(StatedOmega (StatedQuadPlus m K)), IsPGroup p ↥U ∧
      ∀ v : Fin m ⊕ Fin m → K,
        (∀ u ∈ U, ((u : GL (Fin m ⊕ Fin m) K) : Matrix _ _ K) *ᵥ v = v) →
          v ∈ Submodule.span K {(Pi.single (Sum.inl ⟨0, by omega⟩) 1 : Fin m ⊕ Fin m → K)} := by
  let i0 : Fin m := ⟨0, by omega⟩
  let e : Fin m ⊕ Fin m → K := Pi.single (Sum.inl i0) 1
  have he0 : e ≠ 0 := by
    intro h
    have h1 : (1 : K) = 0 := by simpa [e] using congr_fun h (Sum.inl i0)
    exact one_ne_zero h1
  have heq : quadPlus m K e = 0 := by
    rw [quadPlus_apply]
    simp [e, Pi.single_apply]
  have hd : 3 ≤ Module.finrank K (Fin m ⊕ Fin m → K) := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]
    omega
  refine ⟨(LomGLPlus hm e).subgroupOf (StatedOmega (StatedQuadPlus m K)),
    isPGroup_lomGLPlus_subgroupOf p hm e, ?_⟩
  intro v hv
  refine mem_span_of_forall_eichler_apply_eq (nondegenerate_polarBilin_quadPlus m K) hd heq he0 ?_
  intro w hw
  let g₀ : Gom (quadPlus m K) :=
    ⟨eichler (quadPlus m K) e w, eichler_mem_elementaryGroup (quadPlus m K) e w⟩
  have hg₀ : g₀ ∈ Lom (quadPlus m K) e := mem_Lom.mpr (eichler_mem_rootGroup hw)
  let A : ↥(StatedOmega (StatedQuadPlus m K)) := (statedOmegaPlusEquiv hm).symm g₀
  have hA : (A : GL (Fin m ⊕ Fin m) K) ∈ LomGLPlus hm e :=
    Subgroup.mem_map.mpr ⟨A, Subgroup.mem_map.mpr ⟨g₀, hg₀, rfl⟩, rfl⟩
  have hAU : A ∈ (LomGLPlus hm e).subgroupOf (StatedOmega (StatedQuadPlus m K)) := hA
  have h1 : ((A : GL (Fin m ⊕ Fin m) K) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ v
      = g₀.app v := by
    simpa using statedOmegaPlusEquiv_symm_app hm g₀ v
  have h2 := hv A hAU
  rw [h1] at h2
  simpa [Gom.app] using h2

end CFSG.LocalAnalysis.UniquenessCase.UC22.KTabA
