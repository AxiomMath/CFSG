module

public import CFSG.RankThree.GF2n.Smith81.S81CCases
public import CFSG.RankThree.GF2n.Smith81.Sec220Conj

public section

namespace CFSG.RankThree.GF2n.Smith81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80

variable {G : Type} [Group G]

theorem InCaseE4.conj {M Q Z B : Subgroup G} (h : InCaseE4 M Q Z B) (y : G) :
    InCaseE4 (conjSubgroup y M) (conjSubgroup y Q) (conjSubgroup y Z) (conjSubgroup y B) := by
  unfold InCaseE4 at h ⊢
  obtain ⟨t, ht, hc⟩ := h
  exact ⟨y * t * y⁻¹, ht.conj y, hc.conj y⟩

theorem InCaseE5.conj {M Q Z B : Subgroup G} (h : InCaseE5 M Q Z B) (y : G) :
    InCaseE5 (conjSubgroup y M) (conjSubgroup y Q) (conjSubgroup y Z) (conjSubgroup y B) := by
  unfold InCaseE5 at h ⊢
  obtain ⟨t, ht, hc⟩ := h
  exact ⟨y * t * y⁻¹, ht.conj y, hc.conj y⟩

end CFSG.RankThree.GF2n.Smith81
