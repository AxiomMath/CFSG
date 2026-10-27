module

public import CFSG.Quasithin.EmptyFaithful.T1521SBlkMain
public import CFSG.Quasithin.EmptyFaithful.T1521SBlkAut
public import CFSG.Quasithin.EmptyFaithful.T1521SBlkAutTK

public section

namespace CFSG.Quasithin

theorem autFactL2Block1521_holds : AutFactL2Block1521 :=
  autFactL2Block1521_of L21521.l2ModelFacts

theorem dich1521BlockL2_holds : Dich1521BlockL2 :=
  dich1521BlockL2_of autFactL2Block1521_holds

end CFSG.Quasithin
