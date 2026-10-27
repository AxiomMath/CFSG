module

public import CFSG.RankThree.PartTwo.Sec19.Census194.RonanC194Core
public import CFSG.RankThree.PartTwo.Sec19.Census194.Basic
public import CFSG.RankThree.PartTwo.Sec19.Census194.Transport
public import CFSG.RankThree.PartTwo.Sec19.Census194.RankOne

public section

namespace CFSG.RankThree.PartTwo.Sec19.Census194.RonanC194

open CFSG CFSG.RankThree.PartTwo.Sec19

theorem rankOne_holds : Census194RankOne := by
  intro Y _ _ J T hH
  have hodd : Odd (Nat.card (Subgroup.center Y)) :=
    odd_card_center_of_pCore_eq_bot hH.toCensus194RankHyp.pCore_two
  have hJne : J ≠ Subgroup.normalizer ((T : Subgroup Y) : Set Y) := by
    intro hJN
    apply hH.card_ne
    rw [hJN]
    exact card_pCoreOf_normalizer_sylow T
  obtain ⟨T', J', hJ'top, hNJ', hJ'ne⟩ :=
    exists_overgroup_quotient_center T hodd hH.ne_top hH.normalizer_le hJne
  refine ⟨fun f hm => ?_, fun f hm => ?_, ⟨fun e => ?_⟩⟩
  · rcases eq_normalizer_or_top_psl_two hm T' J' hNJ' with h | h
    · exact hJ'ne h
    · exact hJ'top h
  · rcases eq_normalizer_or_top_psu_three hm T' J' hNJ' with h | h
    · exact hJ'ne h
    · exact hJ'top h
  · rcases eq_normalizer_or_top_alt_five ⟨e⟩ T' J' hNJ' with h | h
    · exact hJ'ne h
    · exact hJ'top h

end CFSG.RankThree.PartTwo.Sec19.Census194.RonanC194
