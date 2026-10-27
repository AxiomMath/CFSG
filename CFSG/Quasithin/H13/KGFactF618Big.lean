module

public import CFSG.Quasithin.H13.KGFactF618B

public section

namespace CFSG.Quasithin.H13.A5

open KGF618 in
theorem factF618Big_holds :
    FactF618Big := by
  intro D _ _ G₁ G₂ _ hc
  rcases hc with h | h | h | h | h | h | h | h | h | h
  · exact conclusion_of_good_top (good_caseFour h)
  · exact conclusion_caseFive h
  · exact conclusion_of_good_top (good_caseSix h)
  · exact conclusion_of_good_top (good_caseSeven h)
  · exact conclusion_caseEight h
  · exact conclusion_caseNine h
  · exact conclusion_of_good_top (good_caseTen h)
  · exact conclusion_caseEleven h
  · exact conclusion_of_good_top (good_caseTwelve h)
  · exact conclusion_caseThirteen h

end CFSG.Quasithin.H13.A5
