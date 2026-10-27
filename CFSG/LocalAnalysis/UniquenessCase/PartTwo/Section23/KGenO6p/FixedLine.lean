module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23c.Transfer
import CFSG.ClassicalGroups.Orthogonal.Omega7ThreeLocalRoot
import CFSG.ClassicalGroups.Orthogonal.StatedOmegaElementary
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23a.RootFix
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23c.SylowLine
public import CFSG.ClassicalGroups.Orthogonal.Eichler
public import CFSG.LieType.Universal.Spin.Forms

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.KGenO6pProof

open CFSG.Open CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin QuadraticMap
open scoped Matrix

private theorem kg6_eichler_pow_two {K : Type} [Field K] [CharP K 2]
    (u w : Fin 3 ⊕ Fin 3 → K) : eichler (quadPlus 3 K) u w ^ 2 = 1 := by
  rw [← ringChar.eq (R := K) 2]
  exact CFSG.ClassicalGroups.Orthogonal.Omega7ThreeLocal.eichler_pow_ringChar
    (quadPlus 3 K) u w

private theorem kg6_isPGroup_lomGLPlus {K : Type} [Field K] [CharP K 2]
    (u : Fin 3 ⊕ Fin 3 → K) :
    IsPGroup 2 ↥((LomGLPlus (m := 3) le_rfl u).subgroupOf
      (StatedOmega (StatedQuadPlus 3 K))) := by
  intro g
  have hmem : ((g : ↥(StatedOmega (StatedQuadPlus 3 K))) : GL (Fin 3 ⊕ Fin 3) K) ∈
      LomGLPlus (m := 3) le_rfl u := g.2
  obtain ⟨a, ha, haA⟩ := Subgroup.mem_map.mp hmem
  obtain ⟨g₀, hg₀, hfg⟩ := Subgroup.mem_map.mp ha
  obtain ⟨w, hw, hgw⟩ := mem_rootGroup.mp (mem_Lom.mp hg₀)
  have hg₀eq : g₀ = ⟨eichler (quadPlus 3 K) u w,
      eichler_mem_elementaryGroup (quadPlus 3 K) u w⟩ := Subtype.ext hgw.symm
  have hg₀pow : g₀ ^ 2 = 1 := by
    rw [hg₀eq]
    refine Subtype.ext ?_
    simpa using kg6_eichler_pow_two u w
  have ha_pow : a ^ 2 = 1 := by
    rw [← hfg, ← map_pow, hg₀pow, map_one]
  have hga : a = (g : ↥(StatedOmega (StatedQuadPlus 3 K))) := Subtype.ext haA
  refine ⟨1, ?_⟩
  have hgp : g ^ 2 = 1 := by
    refine Subtype.ext ?_
    rw [Subgroup.coe_pow, Subgroup.coe_one, ← hga, ha_pow]
  simpa using hgp

theorem sylowFixedLine_omegaPlusSix (K : Type) [Field K] [Finite K] [CharP K 2] :
    CFSG.LocalAnalysis.UniquenessCase.UC22.KTabC.SylowFixedLine
      (StatedOmega (StatedQuadPlus 3 K)) (Pi.single (Sum.inl 0) 1) := by
  let e : Fin 3 ⊕ Fin 3 → K := Pi.single (Sum.inl 0) 1
  have he0 : e ≠ 0 := by
    intro h
    have h1 : (1 : K) = 0 := by simpa [e] using congr_fun h (Sum.inl 0)
    exact one_ne_zero h1
  have heq : quadPlus 3 K e = 0 := by
    rw [quadPlus_apply]
    simp [e, Pi.single_apply]
  have hd : 3 ≤ Module.finrank K (Fin 3 ⊕ Fin 3 → K) := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]
    omega
  refine CFSG.LocalAnalysis.UniquenessCase.UC22.KTabC.sylowFixedLine_of_isPGroup
    ((LomGLPlus (m := 3) le_rfl e).subgroupOf (StatedOmega (StatedQuadPlus 3 K)))
    (kg6_isPGroup_lomGLPlus e) e ?_
  intro v hv
  refine CFSG.LocalAnalysis.UniquenessCase.UC22.KTabA.mem_span_of_forall_eichler_apply_eq
    (nondegenerate_polarBilin_quadPlus 3 K) hd heq he0 ?_
  intro w hw
  let g₀ : Gom (quadPlus 3 K) :=
    ⟨eichler (quadPlus 3 K) e w, eichler_mem_elementaryGroup (quadPlus 3 K) e w⟩
  have hg₀ : g₀ ∈ Lom (quadPlus 3 K) e := mem_Lom.mpr (eichler_mem_rootGroup hw)
  let A : ↥(StatedOmega (StatedQuadPlus 3 K)) := (statedOmegaPlusEquiv (m := 3) le_rfl).symm g₀
  have hA : (A : GL (Fin 3 ⊕ Fin 3) K) ∈ LomGLPlus (m := 3) le_rfl e :=
    Subgroup.mem_map.mpr ⟨A, Subgroup.mem_map.mpr ⟨g₀, hg₀, rfl⟩, rfl⟩
  have hAU : A ∈ (LomGLPlus (m := 3) le_rfl e).subgroupOf (StatedOmega (StatedQuadPlus 3 K)) :=
    hA
  have h1 : ((A : GL (Fin 3 ⊕ Fin 3) K) : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K) *ᵥ v
      = g₀.app v := by
    simpa using statedOmegaPlusEquiv_symm_app (m := 3) le_rfl g₀ v
  have h2 := hv A hAU
  rw [h1] at h2
  simpa [Gom.app] using h2

end CFSG.LocalAnalysis.UniquenessCase.UC22.KGenO6pProof
