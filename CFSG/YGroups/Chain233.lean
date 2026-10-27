module

public import CFSG.YGroups.Defs

public section

namespace CFSG.YGroups

theorem rels_y222_y232 : ∀ w ∈ yRels 2 2 2, w.map (shiftAt 4) ∈ yRels 2 3 2 := by decide

theorem rels_y232_y233 : ∀ w ∈ yRels 2 3 2, w.map (shiftAt 7) ∈ yRels 2 3 3 := by decide

theorem rels_y233_y333 : ∀ w ∈ yRels 2 3 3, w.map (shiftAt 2) ∈ yRels 3 3 3 := by decide

end CFSG.YGroups
