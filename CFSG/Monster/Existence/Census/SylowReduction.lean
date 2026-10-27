module

public import CFSG.Monster.Existence.Simple

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.Existence.Census

open CFSG CFSG.Monster CFSG.Monster.Griess CFSG.Monster.Visible CFSG.Monster.Generated Subgroup

theorem cent_xGmat_eq : cent xGmat = Gvis.subgroupOf Gmat := by
  ext g
  rw [Subgroup.mem_subgroupOf, ← map_cent_xGmat]
  exact ⟨fun h => ⟨g, h, rfl⟩, fun ⟨g', hg', e⟩ => by
    have := Gmat.subtype_injective e
    rwa [← this]⟩

theorem exists_conj_involution_mem_Gvis
    (t : Gmat) (ht : orderOf t = 2) :
    ∃ c : Gmat, ∃ f : Gvis,
      (f : SpaceB ≃ₗ[ℚ] SpaceB) = ((c * t * c⁻¹ : Gmat) : SpaceB ≃ₗ[ℚ] SpaceB) ∧
      f * f = 1 ∧ f ≠ 1 := by
  obtain ⟨⟨c, hc, hc2⟩, -⟩ := (generated_group_Sylow_two_reduction.2.2.2.2.1 t ht)
  rw [cent_xGmat_eq, Subgroup.mem_subgroupOf] at hc
  refine ⟨c, ⟨_, hc⟩, rfl, ?_, ?_⟩
  · apply Subtype.ext
    have h := (orderOf_eq_prime_iff.1 hc2).1
    have h' : ((c * t * c⁻¹ : Gmat) : SpaceB ≃ₗ[ℚ] SpaceB) ^ 2 = 1 := by
      rw [← Subgroup.coe_pow, h]
      rfl
    simpa [pow_two] using h'
  · intro h
    have h1 : (c * t * c⁻¹ : Gmat) = 1 := Subtype.ext (by
      have := congrArg Subtype.val h
      simpa using this)
    exact (orderOf_eq_prime_iff.1 hc2).2 h1

end CFSG.Monster.Existence.Census
