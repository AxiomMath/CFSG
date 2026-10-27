module

public import CFSG.Quasithin.Vol2.Ch12Sec4Statements

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint

theorem lemma12_4_3_two_of (h1229 : Stmt12_2_9) (h1243 : Lemma12_4_3_one) :
    Lemma12_4_3_two := by
  intro G _ _ T L V hcx
  exact (h1229 G T L V hcx.hyp).2 (h1243 G T L V hcx)

end CFSG.Quasithin.H13
