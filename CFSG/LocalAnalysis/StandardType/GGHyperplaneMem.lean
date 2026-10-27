module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveIdentDefs

public section

namespace CFSG.StandardType

theorem mem_ggHyperplane_iff' {G : Type} [Group G] {Bs : Subgroup G} {r : MulAut ↥Bs}
    (z : ↥Bs) : (z : G) ∈ ggHyperplane Bs r ↔ r z = z := by
  constructor
  · rintro ⟨w, hw, hwz⟩
    have hw' : w = z := Subtype.ext hwz
    subst hw'
    exact hw
  · intro h
    exact ⟨z, h, rfl⟩

end CFSG.StandardType

end
