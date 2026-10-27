module

public import CFSG.RankThree.PartOne.K133Spor.HNClassB

public section

namespace CFSG.RankThree.PartOne.K133Spor

open CFSG.RankThree.PartOne.K133 CFSG.RankThree.PartOne.S13K

theorem hnKleinPlaneFree : HNKleinPlaneFree :=
  hnKleinPlaneFree_of_classB hnClass_t4J

theorem kf133ResMaxAt_leaf6_hn_proved
    (hTypes : ∀ r, 9 ≤ r → r ≤ 12 → KF132Types r) : KF133ResMaxAt (leaf6 .HN) :=
  kf133ResMaxAt_leaf6_hn hnKleinPlaneFree hTypes

end CFSG.RankThree.PartOne.K133Spor
