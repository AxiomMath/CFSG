module

public import CFSG.OddTranspositions.Blocks

public section

namespace CFSG.OddTranspositions

open CFSG.Timmesfeld

variable {G : Type*} [Group G]

theorem exists_mem_blockClass_of_mem {D α : Set G}
    (hcls : ∃ d₀ : G, D = {g | IsConj d₀ g})
    (hα : IsBlock D α) {d : G} (hd : d ∈ D) :
    ∃ β ∈ blockClass α, d ∈ β := by
  obtain ⟨a, ha⟩ := hα.nonempty
  have haD : a ∈ D := hα.subset ha
  obtain ⟨g, hg⟩ := isConj_iff.mp (CFSG.Timmesfeld.isConj_of_isClass hcls haD hd)
  exact ⟨(fun x => g * x * g⁻¹) '' α, mem_blockClass_iff.mpr ⟨g, rfl⟩, ⟨a, ha, hg⟩⟩

end CFSG.OddTranspositions
