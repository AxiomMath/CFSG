module

public import CFSG.Quasithin.Background.E6TwentyFiveB
public import CFSG.Quasithin.Background.E6TwentyFiveG
public import CFSG.Quasithin.Background.GoldschmidtTDE68Alt

public section

namespace CFSG.Quasithin

namespace E6

open CFSG.Open CFSG.QuasithinUnique

theorem e625_of_rest (h624 : E624Stmt) (h611 : E611Strong) (hN2 : E625NotTwo) : E625Stmt :=
  e625_of h624 h611 e625SLeTwo_holds hN2

theorem e625NotTwo_of_rest (hlist : Lemma115_3_List) (h621 : E621Stmt) (hCent : E68CentComp)
    (hBlock : E625NotTwoBlock) : E625NotTwo :=
  e625NotTwo_of hlist h621 hCent e68AltRank hBlock

end E6

end CFSG.Quasithin
