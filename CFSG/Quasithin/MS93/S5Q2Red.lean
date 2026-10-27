module

public import CFSG.Quasithin.MS93.S5Q2X52Cent
public import CFSG.Quasithin.MS93.S5Q2Even

public section

namespace CFSG.Quasithin.MS93.S5Q2

theorem q2CentEven_of_q2Cent (hq2 : S5B.Q2Cent) : Q2CentEven :=
  fun G _ _ M T L h hmin hb F _ _ a hd _ _ _ => hq2 G M T L h hmin hb F _ _ a hd

theorem q2CentEven_of_q2CentUC (h32 : S32) (H : Q2CentUC) : Q2CentEven :=
  q2CentEven_of_q2Cent (q2Cent_of_q2CentUC h32 H)

theorem q2Cent55_of_q2CentUC (h32 : S32) (H : Q2CentUC) : Q2Cent55 :=
  q2Cent55_of_q2CentEven (q2CentEven_of_q2CentUC h32 H)

end CFSG.Quasithin.MS93.S5Q2
