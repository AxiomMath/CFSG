module

public import CFSG.Quasithin.Vol2.GoldschmidtF431UnDatumFour
public import CFSG.Quasithin.Vol2.GoldschmidtF431UnOutLieMain

public section

namespace CFSG.Quasithin.H13.F431.Un


theorem f431Rank2At_psu4 : F431Rank2At .PSU 4 :=
  f431Rank2At_psu4_of_outLie fun f hf => f431UnOutLieProp_four f hf

end CFSG.Quasithin.H13.F431.Un
