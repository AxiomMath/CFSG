module

public import CFSG.RankThree.PartTwo.Sec4.Ronan148RH1Alt
public import CFSG.RankThree.PartTwo.Sec4.Ronan148RH1A11
public import CFSG.RankThree.PartTwo.Sec4.Ronan148RH1RuJ4
public import CFSG.RankThree.PartTwo.Sec4.Ronan148RH1Co
public import CFSG.RankThree.PartTwo.Sec4.Ronan148RH1HNTh
public import CFSG.RankThree.PartTwo.Sec4.Ronan148RH1SuzLy
public import CFSG.RankThree.PartTwo.Sec4.Ronan148RH1Small
public import CFSG.RankThree.PartTwo.Sec4.Ronan148RH1MJH
public import CFSG.RankThree.PartTwo.Sec4.Ronan148RH1Move
public import CFSG.RankThree.PartTwo.Sec4.Ronan148RH1Mathieu
public import CFSG.RankThree.PartTwo.Sec4.Ronan148RH1J3
public import CFSG.RankThree.PartTwo.Sec4.Ronan148RH1ON

public section

namespace CFSG.RankThree.PartTwo.Sec4.Ronan148R

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.RankThree.PartTwo.Sec4.RonanK429 CFSG.RankThree.PartTwo.Sec4.Ronan148S

section Five


theorem k427Five
    : ∀ n : ℕ, 5 ≤ n → n ≤ 12 → RowOf427 (alternatingGroup (Fin n)) := by
  intro n hn5 hn
  by_cases h8 : n = 8
  · subst h8
    exact rowOf427_alt8
  by_cases h11 : n = 11
  · subst h11
    exact rowOf427_alt11
  exact rowOf427_alternating hn5 hn h8 h11

end Five

section Six


theorem k427Six
    : ∀ s ∈ sporadics42, RowOf427 (Spor s) := by
  intro s hs
  simp only [sporadics42, List.mem_cons, List.mem_nil_iff, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact rowOf427_m11
  · exact rowOf427_m12
  · exact rowOf427_m22
  · exact rowOf427_m23
  · exact rowOf427_m24
  · exact rowOf427_j1
  · exact rowOf427_j2
  · exact rowOf427_j3
  · exact rowOf427_j4
  · exact rowOf427_mcl
  · exact rowOf427_ly
  · exact rowOf427_hs
  · exact rowOf427_he
  · exact rowOf427_suz
  · exact rowOf427_ru
  · exact rowOf427_on
  · exact rowOf427_co3
  · exact rowOf427_co2
  · exact rowOf427_hn
  · exact rowOf427_th

end Six

end CFSG.RankThree.PartTwo.Sec4.Ronan148R

end
