module

public import CFSG.StronglyEmbedded.SteinbergBUConjugateAction
public import CFSG.Assembly.LowTwoRankDefs

public section

namespace CFSG.StronglyEmbedded

open Subgroup CFSG.StronglyEmbedded.SteinbergBU

variable {G : Type*} [Group G]

theorem map_subtype_conjugate (K : Subgroup G) (A : Subgroup K) (u : K) :
    (conjugate A u).map K.subtype = conjugate (A.map K.subtype) (u : G) := by
  ext y
  rw [mem_conjugate_iff, mem_map, mem_map]
  constructor
  · rintro ⟨z, hz, rfl⟩
    rw [mem_conjugate_iff] at hz
    exact ⟨_, hz, rfl⟩
  · rintro ⟨w, hw, hwy⟩
    have hwy' : (w : G) = u * y * (u : G)⁻¹ := hwy
    have hyK : y ∈ K := by
      have : y = (u : G)⁻¹ * (w : G) * u := by
        rw [hwy']
        group
      rw [this]
      exact mul_mem (mul_mem (inv_mem u.2) w.2) u.2
    refine ⟨⟨y, hyK⟩, ?_, rfl⟩
    rw [mem_conjugate_iff]
    have : u * ⟨y, hyK⟩ * u⁻¹ = w := Subtype.ext (by
      simp only [coe_mul, coe_inv]
      exact hwy'.symm)
    rw [this]
    exact hw

end CFSG.StronglyEmbedded
