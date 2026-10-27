module

public import CFSG.RankThree.GF2n.Stroth80.Sec92Quot
public import CFSG.RankThree.GF2n.Stroth80.Sec92SplitN
public import CFSG.RankThree.GF2n.Stroth80.HeringSec91QB
public import CFSG.RankThree.GF2n.Stroth80.HeringSec91Cent
public import CFSG.RankThree.GF2n.Stroth80.HeringSec91N5

public section

namespace CFSG.RankThree.GF2n.Stroth80


theorem stroth91_of_34 (h34 : Stroth34Statement) (h311a : Stroth311aStatement)
    (h311bComm : Stroth311bCommStatement) : Stroth91Statement :=
  ⟨stroth91a, stroth91b_of_steps h34 h311a (sec9NComm_of_311b h34 h311bComm)
    (step91OrderQB_of h34) (step91OrderVQB_of h34) (step91Inter_of h34)
    (step91MixedComm_of h34), stroth91c_of_34 h34⟩

theorem stroth92_of_34 (h34 : Stroth34Statement) (h311a : Stroth311aStatement)
    (h311bComm : Stroth311bCommStatement) (h311bCard : Stroth311bCardStatement) :
    Stroth92Statement :=
  have hA : Sec9AExistsStatement := sec9AExists_of h34 h311a (sec9NComm_of_311b h34 h311bComm)
  have h91 : Stroth91Statement := stroth91_of_34 h34 h311a h311bComm
  stroth92_of_steps hA h91.2.1
    (step92Nontriv_of h34 hA h91.2.1 (sec9NGeFive_of h34 h311a h311bComm h311bCard)
      (step91OrderQB_of h34) (step91OrderVQB_of h34))
    step92Quot (step92Split_of h34 h311a h311bComm h311bCard)

end CFSG.RankThree.GF2n.Stroth80
