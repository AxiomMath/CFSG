module

public import CFSG.Quasithin.MS93.S5Stmt
public import CFSG.Quasithin.MS93.M15Lift

public section

namespace CFSG.Quasithin.MS93.S5

theorem sp4Lift : Sp4Lift := fun G _ _ M T L h k F _ _ a hd =>
  sp4Lift_holds G M T L h k F _ _ a hd

end CFSG.Quasithin.MS93.S5
