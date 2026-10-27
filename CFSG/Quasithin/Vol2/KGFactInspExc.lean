module

public import CFSG.Quasithin.Vol2.KGFactInspExcG2
public import CFSG.Quasithin.Vol2.KGFactInspExcD4
public import CFSG.Quasithin.Vol2.KGFactInspExcF4

public section

namespace CFSG.Quasithin.H13.KGInsp4316

open CFSG.Quasithin.H13.KGInsp4316.Exc

theorem insp4316OutLieExc_holds :
    Insp4316OutLieExc := by
  intro X _ _ S R K n x h hRS ⟨f, hcase⟩ _ _ p hp hp2 hpn _ _
  have h2 : 2 ≤ CFSG.Open.pRank p S := by
    rcases hcase with ⟨-, hm⟩ | ⟨-, hm⟩ | ⟨-, -, hm⟩
    · exact two_le_pRank_g2 h hRS hm hp hpn
    · exact two_le_pRank_d4 h hRS hm hp hp2 hpn
    · exact two_le_pRank_f4 h hRS hm hp hp2 hpn
  exact concl_of_two_le_pRank h hRS hp hp2 hpn h2

end CFSG.Quasithin.H13.KGInsp4316
