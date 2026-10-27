module

public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP1
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP6
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP7
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP8
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP8Rho
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP9
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP10Main

public section

namespace CFSG.Quasithin.H13.F431.U42Aut

open CFSG.Quasithin.H13.F431.U42

theorem u42AutHalf :
    U42AutHalf :=
  u42AutHalf_of_pieces u42AutModelGood u42AutNorm u42AutSylow u42AutFusion u42AutNotExtremal
    u42AutFusionZ u42AutInv u42AutF54 u42AutF55 u42AutF56 (u42AutIdent_of_rho u42AutRho)

end CFSG.Quasithin.H13.F431.U42Aut
