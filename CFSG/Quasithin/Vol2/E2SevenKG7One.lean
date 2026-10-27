module

public import CFSG.Quasithin.Vol2.E2SevenKG7OneMember
public import CFSG.Quasithin.Vol2.E2SevenKG7Close

public section

namespace CFSG.Quasithin

namespace E2

theorem e27Sp4One_holds : E27Sp4One := by
  intro G _ _ X T M K V h hker hKX hXN hC hKT hSp hD hMK hn hV4
  exact exists_isInIHTVC_sp4_one h hker hKX hXN hC hKT hSp hD hMK hn hV4

theorem e27Sp4_holds : E27Sp4 :=
  e27Sp4_of_one e27Sp4One_holds

end E2

end CFSG.Quasithin

end
