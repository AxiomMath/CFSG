module

public import CFSG.GroupTheory.FusionFamilyControl
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Assembly.RankThreeEvenDefs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.GroupTheory Subgroup

theorem FamilyControlsFusion.of_le_mem {G : Type} [Group G] {F F' : Set (Subgroup G)}
    {P : Subgroup G} (h : FamilyControlsFusion F P)
    (hle : ∀ H ∈ F, ∃ H' ∈ F', H ≤ H') : FamilyControlsFusion F' P := by
  intro x y hx hy hc
  refine Relation.EqvGen.mono (fun a b hab => ?_) x y (h x y hx hy hc)
  obtain ⟨ha, hb, H, hH, g, hg, rfl⟩ := hab
  obtain ⟨H', hH', hHH'⟩ := hle H hH
  exact ⟨ha, hb, H', hH', g, hHH' hg, rfl⟩

theorem exists_maxTwoLocal_le_of_isTwoLocal {G : Type} [Group G] [Finite G] {H : Subgroup G}
    (hH : IsTwoLocal H) : ∃ N : Subgroup G, IsMaxTwoLocalSubgroup N ∧ H ≤ N := by
  haveI : Finite (Subgroup G) := Finite.of_injective _ SetLike.coe_injective
  obtain ⟨N, hHN, hmax⟩ :=
    Finite.exists_le_maximal (p := fun K : Subgroup G => IsTwoLocal K) hH
  exact ⟨N, ⟨hmax.1, fun K hK hNK => le_antisymm (hmax.2 hK hNK) hNK⟩, hHN⟩

end CFSG.LocalAnalysis.UniquenessCase.UC22

