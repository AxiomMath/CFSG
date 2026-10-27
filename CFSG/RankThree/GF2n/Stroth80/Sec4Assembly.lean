module

public import CFSG.RankThree.GF2n.Stroth80.Sec4ClassicalFacts
public import CFSG.RankThree.GF2n.Stroth80.Sec41iiTensorMain
public import CFSG.RankThree.GF2n.Stroth80.Sec41iiPointNonsingular

public section

namespace CFSG.RankThree.GF2n.Stroth80

theorem stroth45_of_pointNonsingular (h34 : Stroth34Statement) (h310 : Stroth310Statement)
    (h44 : Stroth44Statement) (hNS : ClassicalPointNonsingularStatement) : Stroth45Statement :=
  stroth45_of_nonsingular h34 h310 h44 hNS classicalOrderFourStatement_holds
    omegaMinusFourSylowStatement_holds

theorem stroth45_of_44 (h34 : Stroth34Statement) (h310 : Stroth310Statement)
    (h44 : Stroth44Statement) : Stroth45Statement :=
  stroth45_of_pointNonsingular h34 h310 h44 classicalPointNonsingularStatement_holds

end CFSG.RankThree.GF2n.Stroth80
