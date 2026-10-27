module

public import CFSG.RankThree.GF2n.Tim81.HBar
public import CFSG.RankThree.GF2n.Tim81.Setting

public section

namespace CFSG.RankThree.GF2n.Tim81

open CFSG CFSG.CGT.Timmesfeld75

@[expose] def HA5Statement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M V : Subgroup G), RootHyp M V → ∀ g : G,
    IsHMember M V (Pc M V ⊔ conjSubgroup g (Pc M V)) →
      V ≤ inSubgroup (pCore 2) (Pc M V ⊔ conjSubgroup g (Pc M V)) →
        IsEmpty (HBar V (Pc M V ⊔ conjSubgroup g (Pc M V)) ≃* alternatingGroup (Fin 5))

end CFSG.RankThree.GF2n.Tim81
