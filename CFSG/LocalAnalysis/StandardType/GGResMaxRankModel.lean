module

public import CFSG.LocalAnalysis.StandardType.GGResMaxRankDefs
public import CFSG.LocalAnalysis.StandardType.GGResLeaves

public section

namespace CFSG.StandardType

open CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def GGResMaxRankModelInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (y : G) (K : Subgroup G), GGResHyp p B Bs x L D J y K → ∀ [Fact p.Prime],
    (GGResRowAt ggRowMaxRank p J L ∨ GGResRowAt ggRowMaxRank p J K) →
      GGResMaxRankDatum p Bs L J K ggMaxRankSelAny

end CFSG.StandardType

end
