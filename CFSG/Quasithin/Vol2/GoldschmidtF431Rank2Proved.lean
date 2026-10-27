module

public import CFSG.Quasithin.Vol2.GoldschmidtF431Rank2Wire
public import CFSG.Quasithin.Vol2.GoldschmidtF431G2Thm
public import CFSG.Quasithin.Vol2.GoldschmidtF431D4qFinal
public import CFSG.Quasithin.Vol2.GoldschmidtF431TwoF4Thm
public import CFSG.Quasithin.Vol2.GoldschmidtF431UnFour
public import CFSG.Quasithin.Vol2.GoldschmidtF431Un5Std
public import CFSG.Quasithin.Vol2.GoldschmidtF431Un5Rank2
public import CFSG.Quasithin.Vol2.GoldschmidtF431Un5OutLieMain

public section

namespace CFSG.Quasithin.H13.F431

set_option linter.unusedSectionVars false


theorem f431Rank2_proved : F431Rank2 :=
  f431Rank2_of_at f431Rank2At_psl3 f431Rank2At_psp G2.f431Rank2At_g2 D4q.f431Rank2At_d4q
    TwoF4.f431Rank2At_twistedF4 Un.f431Rank2At_psu4 (Un.f431Rank2At_psu5_of_inputs
        Un.f431UnOutLieProp_five Un.un5StdDatum)

end CFSG.Quasithin.H13.F431
