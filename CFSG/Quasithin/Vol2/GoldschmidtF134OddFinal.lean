module

public import CFSG.Quasithin.Vol2.GoldschmidtF134OddLieOrders
public import CFSG.Quasithin.Vol2.GoldschmidtF134OddLieU3E
public import CFSG.Quasithin.Vol2.GoldschmidtF134OddLieL2E
public import CFSG.Quasithin.Vol2.GoldschmidtF134OddLieSz
public import CFSG.Quasithin.Vol2.GoldschmidtF134OddLieL3EQ
public import CFSG.Quasithin.Vol2.GoldschmidtF134OddLieG2Q
public import CFSG.Quasithin.Vol2.GoldschmidtF134OddLieD4Q
public import CFSG.Quasithin.Vol2.GoldschmidtF134OddLieF4Q
public import CFSG.Quasithin.Vol2.GoldschmidtF134OddLieSp4Q
public import CFSG.Quasithin.Vol2.GoldschmidtF134OddLieL2OQ
public import CFSG.Quasithin.Vol2.GoldschmidtF134OddLieU3OQ
public import CFSG.Quasithin.Vol2.GoldschmidtF134OddLieL3OMain
public import CFSG.Quasithin.Vol2.GoldschmidtF134OddTits
public import CFSG.Quasithin.Vol2.GoldschmidtF134OddNormalAsm
public import CFSG.Quasithin.Vol2.GoldschmidtF134OddSporMain
public import CFSG.Quasithin.Background.F6CatInstances

public section

namespace CFSG.Quasithin.H13.NQCore

theorem facts134Odd_proved
    : Facts134Odd :=
  facts134Odd_of_normal (facts134OddNormal_of_cases CFSG.Quasithin.F6.nativeTheoremCSection
    CFSG.QuasithinUnique.Vol2Native.a36CoreForSQTKCat_proved facts134OddSporadic_proved
    ({ alt := lieAlt,
       psl45 := liePsl45,
       psl2Odd := liePsl2Odd,
       psl2Even := liePsl2Even,
       sz := lieSz,
       psu3Even := liePsu3Even,
       psl3Even := liePsl3Even,
       psu3Odd := liePsu3Odd,
       g2Even := lieG2Even,
       d4Even := lieD4Even,
       f4Even := lieF4Even,
       tits := lieTits,
       psp4Even := liePsp4Even,
       psl3Odd := liePsl3Odd_of_simple psl3Odd_simple }))

end CFSG.Quasithin.H13.NQCore
