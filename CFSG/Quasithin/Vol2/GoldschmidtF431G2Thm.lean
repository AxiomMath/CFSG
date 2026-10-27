module

public import CFSG.Quasithin.Vol2.GoldschmidtF431G2Final
public import CFSG.Quasithin.Vol2.GoldschmidtF431G2OutLieMain

public section

namespace CFSG.Quasithin.H13.F431.G2

open CFSG.Quasithin.H13.F431


theorem f431Rank2At_g2 : F431Rank2At .G2 0 :=
  f431Rank2At_g2_of_out fun f _ => f431TwoOutLieProp_g2 f

end CFSG.Quasithin.H13.F431.G2
