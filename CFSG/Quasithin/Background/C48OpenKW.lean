module

public import CFSG.Quasithin.Background.C48Open
public import CFSG.Quasithin.Vol2.KGFactC31Spor
public import CFSG.Quasithin.Vol2.KGFactC31Ru
public import CFSG.Quasithin.Vol2.KGFactC31J4Fin
public import CFSG.Quasithin.Vol2.KGFactJ4M4Card

public section

namespace CFSG.Quasithin.C48

open CFSG.Open hiding StatedSL StatedSp
open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank

variable {G : Type} [Group G] [Finite G]

theorem asc48Statement_of_kw
    (hC41 : ASC41Statement G) (h27 : ASC27Statement G) (hKW : CFSG.Quasithin.KGJ4.J4TwoLocalsKW)
    (hCov : C48SporCoverFact G) : ASC48Statement G :=
  asc48Statement_of_open'' hC41 h27
    (KGC31.inspC31Sporadic_of KGC31.Ru.inspC31SporadicAt_ru
        (KGC31.J4.inspC31SporadicAtJ_j4 hKW CFSG.Quasithin.J4M4Card.card_M4)) hCov

end CFSG.Quasithin.C48
