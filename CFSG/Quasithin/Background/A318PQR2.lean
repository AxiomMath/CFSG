module

public import CFSG.Quasithin.Background.A318PQR1
public import CFSG.Sporadic.Schreier.J4SThree

public section

namespace CFSG.Quasithin

open CFSG.Sporadic.J4Schreier CFSG.Sporadic.J4

theorem j4OrderThreeCentralizerBound_holds :
    J4OrderThreeCentralizerBound :=
  fun _ hk ok => card_centralizer_three (K_le_H hk) ok

theorem qSporOutTwo_holds :
    QSporOutTwo :=
  qSporOutTwo_of_orderThreeCentralizerBound j4OrderThreeCentralizerBound_holds

end CFSG.Quasithin
