module

public import CFSG.Quasithin.Vol2.GoldschmidtF134OddSporCases
public import CFSG.Quasithin.Vol2.GoldschmidtF134OddSporJ4

public section

namespace CFSG.Quasithin.H13.NQCore

theorem noOddConfigSpor_j4 :
    NoOddConfigSpor .J4 :=
  noOddConfigSpor_of_noPowerOvergroup noPowerOvergroup_j4

theorem facts134OddSporadic_proved :
    Facts134OddSporadic where
  m11 := noOddConfigSpor_m11
  m12 := noOddConfigSpor_m12
  m22 := noOddConfigSpor_m22
  m23 := noOddConfigSpor_m23
  m24 := noOddConfigSpor_m24
  j1 := noOddConfigSpor_j1
  j2 := noOddConfigSpor_j2
  hs := noOddConfigSpor_hs
  he := noOddConfigSpor_he
  ru := noOddConfigSpor_ru
  j4 := noOddConfigSpor_j4

end CFSG.Quasithin.H13.NQCore
