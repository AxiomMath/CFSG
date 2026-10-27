module

public import CFSG.Quasithin.Vol2.KGFactC31Spor
public import CFSG.Quasithin.Vol2.KGFactC31Ru
public import CFSG.Quasithin.Vol2.KGFactC31J4Fin
public import CFSG.Quasithin.Vol2.KGFactJ4M4Card

public section

namespace CFSG.Quasithin.KGC31

theorem inspC31Sporadic_holds'
    (hKW : CFSG.Quasithin.KGJ4.J4TwoLocalsKW) : CFSG.Quasithin.InspC31Sporadic :=
  inspC31Sporadic_of Ru.inspC31SporadicAt_ru
      (J4.inspC31SporadicAtJ_j4 hKW CFSG.Quasithin.J4M4Card.card_M4)

end CFSG.Quasithin.KGC31

end
