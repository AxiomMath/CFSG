module

public import CFSG.RankThree.GF2n.Tim79aWCQ
public import CFSG.RankThree.GF2n.Tim81S34
public import CFSG.RankThree.GF2n.Tim81RootReduce

public section

namespace CFSG.RankThree.GF2n.Tim81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Tim78

variable {G : Type} [Group G]

namespace Hyp3

variable [Finite G] {M V Q P : Subgroup G} (H : Hyp3 M V Q P)
include H

theorem citedT79_of_tim79aWCQ (h : Tim79aStatementWCQ) (hwcQ : WeaklyClosedIn V Q)
    (hnwc : ¬ WeaklyClosedIn V M) : CitedT79 V P := by
  intro K hPK hK
  rcases h G H.o2 M H.maxLocal H.fitting V H.maxAb H.elemAb H.ti H.four (H.hQ ▸ hwcQ) with
    hwc | h2
  · exact absurd hwc hnwc
  · refine h2 K hK ?_
    rw [← H.hQ, ← H.hP]
    exact hPK

theorem rootTypeStep_of_tim79aWCQ (h : Tim79aStatementWCQ) (hwcQ : WeaklyClosedIn V Q)
    (hnwc : ¬ WeaklyClosedIn V M) : RootTypeStep M V :=
  H.toRootCore.rootTypeStep_of_citedT79 (H.citedT79_of_tim79aWCQ h hwcQ hnwc)

theorem weaklyClosed_or_rootType_of_wcq (h : Tim79aStatementWCQ) (hwcQ : WeaklyClosedIn V Q) :
    WeaklyClosedIn V M ∨ IsRootTypeTI V := by
  by_cases hwc : WeaklyClosedIn V M
  · exact Or.inl hwc
  · exact Or.inr (H.toRootCore.rootTypeStep_iff.mp (H.rootTypeStep_of_tim79aWCQ h hwcQ hwc))

end Hyp3

end CFSG.RankThree.GF2n.Tim81
