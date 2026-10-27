module

public import CFSG.RankThree.GF2n.Tim81.Basic
public import CFSG.RankThree.GF2n.Tim81.Setting
public import CFSG.RankThree.GF2n.Tim81S34WCQ

public section

namespace CFSG.RankThree.GF2n.Tim81

open CFSG CFSG.CGT.Timmesfeld75

variable {G : Type} [Group G] {M V : Subgroup G}

theorem _root_.CFSG.CGT.Timmesfeld75.WeaklyClosedIn.of_le {V X Y : Subgroup G}
    (h : WeaklyClosedIn V X) (hVY : V ≤ Y) (hYX : Y ≤ X) : WeaklyClosedIn V Y :=
  ⟨hVY, fun g hg => h.2 g (hg.trans hYX)⟩

namespace Hyp

theorem toHyp3 (h : Hyp M V) (h4 : 4 ≤ Nat.card V) :
    Hyp3 M V (inSubgroup (pCore 2) M) (Pc M V) :=
  ⟨h.o2, h.maxLocal, h.fitting, h.maxAb, h.elem, h.ti, h4, rfl, rfl⟩

theorem isRootTypeTI [Finite G] (h79 : Tim79aStatementWCQ) (h : Hyp M V) (h4 : 4 ≤ Nat.card V)
    (hwcQ : WeaklyClosedIn V (inSubgroup (pCore 2) M)) (hnwc : ¬ WeaklyClosedIn V M) :
    Tim78.IsRootTypeTI V :=
  ((h.toHyp3 h4).weaklyClosed_or_rootType_of_wcq h79 hwcQ).resolve_left hnwc

theorem rootHyp [Finite G] (h79 : Tim79aStatementWCQ) (h : Hyp M V) (h4 : 4 ≤ Nat.card V)
    (hwcQ : WeaklyClosedIn V (inSubgroup (pCore 2) M)) (hnwc : ¬ WeaklyClosedIn V M) :
    RootHyp M V :=
  { h with
    four_le_card := h4
    weaklyClosed_P := hwcQ.of_le h.le_Pc inf_le_left
    rootType := h.isRootTypeTI h79 h4 hwcQ hnwc
    not_weaklyClosed := hnwc }

end Hyp

end CFSG.RankThree.GF2n.Tim81
