module

public import CFSG.OddTranspositions.Blocks

public section

namespace CFSG.OddTranspositions

variable {G : Type*} [Group G]

theorem mem_normalizer_of_mem_alpha {D α : Set G} (h : IsBlock D α) {a : G} (ha : a ∈ α) :
    a ∈ Subgroup.normalizer α := by
  rw [Subgroup.mem_normalizer_iff_conj_image_eq]
  by_contra hne
  have hna : a ∉ Subgroup.normalizer α := by
    rwa [Subgroup.mem_normalizer_iff_conj_image_eq]
  have hd := h.disjoint_conj hna
  have ha' : a ∈ (fun x => a * x * a⁻¹) '' α := ⟨a, ha, by group⟩
  exact (Set.disjoint_left.mp hd ha) ha'

theorem commute_mul_of_mem_Dalpha {D α β : Set G} (hβ : β ∈ Dalpha D α)
    {a c d : G} (ha : a ∈ α) (hc : c ∈ α) (hd : d ∈ β) :
    Commute (a * c) d := by
  have hcomm := (mem_Dalpha_iff.mp hβ).2.2.2
  exact (hcomm a ha d hd).mul_left (hcomm c hc d hd)

theorem image_mul_mem_alpha {D α : Set G} (h : IsBlock D α) {a c : G} (ha : a ∈ α)
    (hc : c ∈ α) :
    (fun x => a * c * x * (a * c)⁻¹) '' α = α := by
  have hN : a * c ∈ Subgroup.normalizer α :=
    (Subgroup.normalizer α).mul_mem (mem_normalizer_of_mem_alpha h ha)
      (mem_normalizer_of_mem_alpha h hc)
  rw [Subgroup.mem_set_normalizer_iff] at hN
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact (hN y).mp hy
  · intro hx
    have hcalc : a * c * ((a * c)⁻¹ * x * (a * c)) * (a * c)⁻¹ = x := by group
    exact ⟨(a * c)⁻¹ * x * (a * c), (hN _).mpr (by rwa [hcalc]), hcalc⟩

end CFSG.OddTranspositions
