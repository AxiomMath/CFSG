module

public import CFSG.RankThree.PartOne.S13K.KF133One
import CFSG.RankThree.PartOne.HNB.Tools

public section

namespace CFSG.RankThree.PartOne.K133

open CFSG CFSG.Assembly CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
  CFSG.RankThree.PartOne CFSG.RankThree.PartOne.S13K

variable {G : Type} [Group G] [Finite G] {p : ℕ} {A : Subgroup G} {c : G} {L E : Subgroup G}

theorem normalizes_L (h : Sec12Hyp G p A c L E) (hF : Sec12Facts G p A c L E) :
    E ≤ Subgroup.normalizer (L : Set G) := by
  intro x hx
  have hxc : x * c = c * x := (Subgroup.mem_centralizer_iff.mp (h.E_le hx) c h.c_mem).symm
  exact hF.twoB (Subgroup.mem_inf.2
    ⟨HNB.mem_normalizer_zpowers_of_commute hxc, Subgroup.le_normalizer hx⟩)

end CFSG.RankThree.PartOne.K133
