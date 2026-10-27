module

public import CFSG.StronglyEmbedded.UniqueCosetBasic

public section

namespace CFSG.StronglyEmbedded.UniqueCoset

variable {G : Type*} [Group G]

theorem existsUnique_fixed_of_mem {H : Subgroup G} {a : G} (ha : a ∈ H)
    (h : ∀ g : G, g⁻¹ * a * g ∈ H → g ∈ H) : ∃! c : G ⧸ H, a • c = c := by
  refine ⟨((1 : G) : G ⧸ H), ?_, fun c hc => ?_⟩
  · show a • ((1 : G) : G ⧸ H) = ((1 : G) : G ⧸ H)
    rw [smul_coe_eq_iff]
    simpa using ha
  · obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective c
    have hc' : a • (g : G ⧸ H) = g := hc
    have hg := (smul_coe_eq_iff _ a g).mp hc'
    have hgH := h g hg
    rw [QuotientGroup.eq]
    simpa using H.inv_mem hgH

end CFSG.StronglyEmbedded.UniqueCoset
