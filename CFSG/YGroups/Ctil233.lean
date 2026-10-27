module

public import CFSG.YGroups.Defs

public section

namespace CFSG.YGroups

@[expose] def Ctil : Subgroup (YGroup 2 3 3) :=
  Subgroup.closure (yGen 2 3 3 '' {c | c < 9 ∧ c ≠ 2})

theorem yGen_mem_ctil {c : ℕ} (hc : c < 9) (hc2 : c ≠ 2) : yGen 2 3 3 c ∈ Ctil :=
  Subgroup.subset_closure ⟨c, ⟨hc, hc2⟩, rfl⟩

end CFSG.YGroups

end
