module

public import CFSG.Quasithin.Vol2.Ch10SecKRRg
public import CFSG.Quasithin.Vol2.Ch10SecB6Facts

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB

open CFSG.Open CFSG.Quasithin

theorem fact10_2_6Rank_of
    (hLF : A312LeviField) : Fact10_2_6Rank := by
  intro X _ _ B L h
  show KRR.RankGoal B L
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · exact (KRR.rankWit_C2 hLF h).goal
  · exact (KRR.rankWit_C3 h).goal
  · exact (KRR.rankWit_C4 h).goal
  · exact (KRR.rankWit_C5 h).goal
  · exact (KRR.rankWit_C6 h).goal
  · exact (KRR.rankWit_C7 h).goal
  · exact KRR.rankGoal_C8 h
  · exact (KRR.rankWit_C9 h).goal
  · exact (KRR.rankWit_C10 h).goal
  · exact (KRR.rankWit_C11 h).goal
  · exact (KRR.rankWit_C12 h).goal
  · exact (KRR.rankWit_C13 h).goal
  · exact (KRR.rankWit_C14 h).goal
  · exact KRR.rankGoal_C15 h
  · exact (KRR.rankWit_C16 h).goal
  · exact (KRR.rankWit_C17 h).goal
  · exact (KRR.rankWit_C18 h).goal
  · exact (KRR.rankWit_C19 h).goal
  · exact (KRR.rankWit_C20 h).goal

end CFSG.Quasithin.Vol2.Ch10.SecB
