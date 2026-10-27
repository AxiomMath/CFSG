module

public import CFSG.Quasithin.Vol2.Ch10SecQ1Orth
public import CFSG.Quasithin.Vol2.Ch10SecQ1Sp4
public import CFSG.Quasithin.Vol2.Ch10SecQ1G2Two
public import CFSG.Quasithin.Vol2.Ch10SecQ1G2
public import CFSG.Quasithin.Vol2.Ch10SecQ1SU3
public import CFSG.Quasithin.Vol2.Ch10SecQ1M2x
public import CFSG.Quasithin.Vol2.Ch10SecQ1M12

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecA

theorem facts10_1_holds :
    Facts10_1 :=
  ⟨factOrthA5_holds, factSp4TwoNormal_holds, factG2TwoNormal_holds, factB4aG2_holds,
    factB4aG2Derived_holds, factB4aNineTensor_holds, factB4aSU3_holds, factB4aSp4Twisted_holds,
    factB4aM12_holds, factB4aM22_holds, factB4aM23_holds, factB4aM24_holds, factB4aJ2_holds⟩

end CFSG.Quasithin.Vol2.Ch10.SecA
