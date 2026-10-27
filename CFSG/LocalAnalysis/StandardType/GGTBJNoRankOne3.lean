module

public import CFSG.LocalAnalysis.StandardType.GGFieldTwoCornerDefs
public import CFSG.LocalAnalysis.StandardType.GGTBJNoRankOneDefs
public import CFSG.LocalAnalysis.StandardType.GGTPNDefs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

@[expose] def GGTBJNoRankOne3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGConfig 3 B Bs x L D J →
      ¬ GGHasLabel (⟨.A, 1, 3⟩ : LargeEvenLabel) (↥J ⧸ Subgroup.center ↥J)

theorem ggFieldTwoCornerNoSL28_of_noRankOne3 (h : GGTBJNoRankOne3) : GGFieldTwoCornerNoSL28 := by
  intro G _ _ p B Bs x L D J y K hset hlab
  obtain ⟨hcfg, -, -, -, hJK, rfl, -, -⟩ := hset
  exact h G B Bs x L D J hcfg
    (ggHasLabel_quotCenter_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hJK) hlab)

end CFSG.StandardType

end
