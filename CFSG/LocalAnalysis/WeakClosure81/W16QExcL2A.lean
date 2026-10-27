module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenUniqueMax
public import CFSG.Quasithin.Background.E3Defs

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open Subgroup

variable {G : Type} [Group G] [Finite G]

theorem w16q_mQuot_inf (V I : Subgroup G) : E3.mQuot V (V ⊓ I) = E3.mQuot V I := by
  show padicValNat 2 ((V ⊓ I).relIndex V) = padicValNat 2 (I.relIndex V)
  rw [Subgroup.inf_relIndex_left]

theorem w16q_conjSubgroup_le_of_le {A K : Subgroup G} (hA : A ≤ K) {k : G} (hk : k ∈ K) :
    conjSubgroup A k ≤ K := by
  intro x hx
  rw [mem_conjSubgroup_iff] at hx
  have hxk : k * x * k⁻¹ ∈ K := hA hx
  have : x = k⁻¹ * (k * x * k⁻¹) * k := by group
  rw [this]
  exact K.mul_mem (K.mul_mem (K.inv_mem hk) hxk) hk

theorem w16q_map_conjSubgroup {X : Type} [Group X] {K : Subgroup G} (φ : ↥K →* X)
    {V : Subgroup G} (hVK : V ≤ K) {k : G} (hk : k ∈ K) :
    ((conjSubgroup V k).subgroupOf K).map φ =
      CFSG.CGT.Timmesfeld75.conjSubgroup (φ ⟨k, hk⟩)⁻¹ ((V.subgroupOf K).map φ) := by
  ext y
  constructor
  · rintro ⟨w, hw, rfl⟩
    rw [CFSG.CGT.Timmesfeld75.mem_conjSubgroup]
    refine Subgroup.mem_map.2 ⟨⟨k, hk⟩ * w * ⟨k, hk⟩⁻¹, ?_, ?_⟩
    · rw [Subgroup.mem_subgroupOf]
      simpa using mem_conjSubgroup_iff.1 hw
    · simp only [map_mul, map_inv]
      group
  · intro hy
    rw [CFSG.CGT.Timmesfeld75.mem_conjSubgroup] at hy
    obtain ⟨v, hv, hvφ⟩ := Subgroup.mem_map.1 hy
    refine Subgroup.mem_map.2 ⟨⟨k, hk⟩⁻¹ * v * ⟨k, hk⟩, ?_, ?_⟩
    · rw [Subgroup.mem_subgroupOf, mem_conjSubgroup_iff]
      change k * (k⁻¹ * (v : G) * k) * k⁻¹ ∈ V
      have hvV : (v : G) ∈ V := hv
      have h : k * (k⁻¹ * (v : G) * k) * k⁻¹ = (v : G) := by group
      rw [h]
      exact hvV
    · simp only [map_mul, map_inv, hvφ]
      group

end CFSG.LocalAnalysis.WeakClosure81

end
