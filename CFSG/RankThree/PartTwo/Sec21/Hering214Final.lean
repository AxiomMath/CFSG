module

public import CFSG.RankThree.PartTwo.Sec21.Hering214L3Model
public import CFSG.RankThree.PartTwo.Sec21.Hering214Lin2

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL)
open Hering214

theorem item214BarL3_holds : Item214BarL3 := by
  intro X _ _ Ē _ _ h
  rcases h with ⟨n, hn, -, ⟨eL⟩, hC⟩ | ⟨n, hn, he, ⟨eL⟩, hC⟩
  · exact eInvFour_of_typeC hn eL hC
  · obtain ⟨k, hk⟩ := he
    exact eInvFour_of_typeCSL (by omega) eL hC

theorem item214BarL45_holds : Item214BarL45 := by
  intro X _ _ h Ē Ū hd
  exact eInvFourFact_of_psl_two_one h Ē Ū hd

end CFSG.RankThree.PartTwo.Sec21
