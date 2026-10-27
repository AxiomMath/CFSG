module

public import CFSG.OddTranspositions.BlockAction

public section

namespace CFSG.OddTranspositions

variable {G : Type*} [Group G]

theorem image_mul_mem_of_mem_Dalpha {D α β : Set G} (hβ : β ∈ Dalpha D α)
    {a c : G} (ha : a ∈ α) (hc : c ∈ α) :
    (fun x => a * c * x * (a * c)⁻¹) '' β = β := by
  have hfix : ∀ x ∈ β, a * c * x * (a * c)⁻¹ = x := by
    intro x hx
    rw [Commute.eq (commute_mul_of_mem_Dalpha hβ ha hc hx)]
    group
  simpa using Set.image_congr hfix

theorem image_mul_mem_of_mem_perp {D α β : Set G} (h : IsBlock D α)
    (hβ : β ∈ perp D α) {a c : G} (ha : a ∈ α) (hc : c ∈ α) :
    (fun x => a * c * x * (a * c)⁻¹) '' β = β := by
  rcases mem_perp_iff.mp hβ with hβ | rfl
  · exact image_mul_mem_of_mem_Dalpha hβ ha hc
  · exact image_mul_mem_alpha h ha hc

end CFSG.OddTranspositions
