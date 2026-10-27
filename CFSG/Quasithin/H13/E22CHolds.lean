module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtE22NoNProved
public import CFSG.Quasithin.EmptyFaithful.E111L2F
public import CFSG.Quasithin.EmptyFaithful.E22NL2
public import CFSG.Quasithin.Vol2.Ch11SecOE9R
public import CFSG.Quasithin.Vol2.Ch11SecU1EpsOut

public section

namespace CFSG.Quasithin.H13

theorem e22StatementC_holds :
    E2.E22StatementC :=
  E2.E22N.e22StatementC_ofRL2 e22StatementNoN_proved E2.E22N.E111L.e111CoreMultiL2_holds
    (Vol2.Ch11.SecE3.e114ForE22R_of Vol2.Ch11.SecE3.Lie3.e114LieCited_holds
      (Vol2.Ch11.SecB.e114OneRes_of_rest E2.E22N.e114OneResRest_holds))

end CFSG.Quasithin.H13

end
