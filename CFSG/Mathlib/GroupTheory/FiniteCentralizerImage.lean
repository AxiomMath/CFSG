module

public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.Data.Finset.Attr
public import Mathlib.Tactic.Bound.Init

public section

namespace CFSG.GroupTheory

variable {G H : Type*} [Group G] [Group H]

theorem map_centralizer_subtype (K : Subgroup G) (R : Subgroup K) :
    (Subgroup.centralizer (R : Set K)).map K.subtype =
      K ⊓ Subgroup.centralizer (R.map K.subtype : Set G) := by
  ext x
  constructor
  · rintro ⟨g, hg, rfl⟩
    refine ⟨g.2, Subgroup.mem_centralizer_iff.mpr ?_⟩
    rintro y ⟨r, hr, rfl⟩
    exact congrArg Subtype.val (Subgroup.mem_centralizer_iff.mp hg r hr)
  · rintro ⟨hxK, hxC⟩
    refine ⟨⟨x, hxK⟩, Subgroup.mem_centralizer_iff.mpr ?_, rfl⟩
    intro r hr
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hxC r
      (Subgroup.mem_map_of_mem K.subtype hr))

end CFSG.GroupTheory
