module

public import CFSG.Milestones.ASVolI.F411.Cent
public import CFSG.Milestones.ASVolI.F411.aSp4Mat
public import CFSG.Milestones.ASVolI.F411.aSp4Std

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag

theorem burnsideF411a_autCentSylow_Sp4 (K : Type) [Field K] [Finite K] (p : ℕ) [Fact p.Prime]
    [CharP K p] : burnsideF411_AutCentSylow (StatedProj (StatedSp 2 K)) p := by
  intro α S hα
  obtain ⟨P₀, hP₀⟩ := exists_sylow_projUnipotent (K := K) p (r := 2) (by norm_num)
  obtain ⟨x, hx⟩ := MulAction.exists_smul_eq (StatedProj (StatedSp 2 K)) P₀ S
  have hβ : ∀ u ∈ projUnipotent 2 K, ((MulAut.conj x)⁻¹ * α * MulAut.conj x) u = u := by
    intro u hu
    have hxu : x * u * x⁻¹ ∈ (S : Subgroup (StatedProj (StatedSp 2 K))) := by
      rw [← hx, Sylow.coe_subgroup_smul]
      have h1 := Subgroup.smul_mem_pointwise_smul u (MulAut.conj x) (P₀ : Subgroup _)
        (by rw [hP₀]; exact hu)
      rwa [MulAut.smul_def, MulAut.conj_apply] at h1
    rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.conj_apply, hα _ hxu, MulAut.conj_inv_apply]
    group
  obtain ⟨A, σ, hAσ⟩ := burnsideF411a_sp4_standard_of_fix p _ hβ
  obtain ⟨g, hg⟩ := burnsideF411a_sp4_inner_of_fix p A σ (hAσ ▸ hβ)
  refine ⟨x * g * x⁻¹, ?_⟩
  rw [map_mul, map_mul, map_inv, ← hg, ← hAσ]
  group

end CFSG.ASVolI
