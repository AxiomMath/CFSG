module

public import CFSG.LocalAnalysis.StandardType.GGTPNRegimeDefs
public import CFSG.LocalAnalysis.StandardType.GGTPNThmRABase
public import CFSG.LocalAnalysis.StandardType.GGExcRERegimeDefs
public import CFSG.LocalAnalysis.StandardType.GGTPNDefs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

@[expose] def GGFieldTwoCorner : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (y : G) (K : Subgroup G), GGConfig p B Bs x L D J → GGInnerDiagOn Bs L →
    GGInnerDiagOn Bs K → GGNbr p B x D J y K → J ≤ K → p = 3 →
      GGHasLabel ⟨.twA, 5, 1⟩ (K ⧸ Subgroup.center K) →
      (∃ labJ : LargeEvenLabel, LargeEvenInLambda2 labJ ∧ 2 ≤ labJ.n ∧
        GGHasLabel labJ (↥(J.subgroupOf K) ⧸ Subgroup.center ↥(J.subgroupOf K))) →
      GGTPNRankJ (J.subgroupOf K)

end CFSG.StandardType

end
