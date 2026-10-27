module

public import CFSG.Quasithin.Vol2.GoldschmidtF431U42F48Final
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42F48Holds
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42LocMain
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutHalf

public section

namespace CFSG.Quasithin.H13.F431.U42

theorem stmtF431U42_holds :
    StmtF431U42 :=
  stmtF431U42_of_three_inputs' u42F48_holds u42LocalCent_holds U42Aut.u42AutHalf

end CFSG.Quasithin.H13.F431.U42
