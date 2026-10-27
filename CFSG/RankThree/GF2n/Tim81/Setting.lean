module

public import CFSG.RankThree.GF2n.Tim81.Defs
public import CFSG.RankThree.GF2n.Tim78RootType

public section

namespace CFSG.RankThree.GF2n.Tim81

open CFSG CFSG.CGT.Timmesfeld75

variable {G : Type} [Group G]

structure RootHyp (M V : Subgroup G) : Prop extends Hyp M V where
  four_le_card : 4 ≤ Nat.card V
  weaklyClosed_P : WeaklyClosedIn V (Pc M V)
  rootType : Tim78.IsRootTypeTI V
  not_weaklyClosed : ¬ WeaklyClosedIn V M

end CFSG.RankThree.GF2n.Tim81
