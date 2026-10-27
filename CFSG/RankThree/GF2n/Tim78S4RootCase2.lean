module

public import CFSG.RankThree.GF2n.Tim81Hyp4Bridge
public import CFSG.RankThree.GF2n.Tim81RootReduce

public section

namespace CFSG.RankThree.GF2n.Tim78

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.RankThree.GF2n
open scoped commutatorElement

variable {G : Type} [Group G]

namespace Hyp4

variable [Finite G] {M B Q P T : Subgroup G} (H : Hyp4 M B Q P T)
include H

theorem rootStep1_of_not_le_M {g : G} (hgM : ¬ conjSubgroup g B ≤ M) : RootStep1 M B Q g :=
  H.toRootCore.rootStep1_of_not_le_M hgM

end Hyp4

end CFSG.RankThree.GF2n.Tim78
