module

public import CFSG.RankThree.GF2n.Stroth80.Sec94FreeL7
public import CFSG.RankThree.GF2n.Stroth80.Sec94FreeL8
public import CFSG.RankThree.GF2n.Stroth80.Sec92SplitN

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank

theorem step94CNAll_of_gen_notQB (h34 : Stroth34Statement) (h311a : Stroth311aStatement)
    (h311bComm : Stroth311bCommStatement) (h311bCard : Stroth311bCardStatement)
    (hGen : Step94GenStatement) (hNotQB : Step94NotQBStatement) : Step94CNAllStatement :=
  have h92 : Stroth92Statement :=
    stroth92_of_split h34 h311a h311bCard h311bComm (step92Split_of h34 h311a h311bComm h311bCard)
  have hB : Step94ConjVStatement := step94ConjV_of h34 h311a h311bComm
  have hDimQ : Step94DimQStatement := step94DimQ_holds h34 h311a h311bComm
  step94CNAll_of h34 h311a h92 hB hGen (step94CountNu_of h34 h92 hB hNotQB hDimQ)
    (step94SNu_of h34 h92 hB hNotQB hDimQ hGen)

theorem step94EndFree_of_gen_notQB (h34 : Stroth34Statement) (h311a : Stroth311aStatement)
    (h311bComm : Stroth311bCommStatement) (h311bCard : Stroth311bCardStatement)
    (hGen : Step94GenStatement) (hNotQB : Step94NotQBStatement) : Step94EndFreeStatement :=
  step94EndFree_of h34 h311a h311bComm h311bCard
    (stroth92_of_split h34 h311a h311bCard h311bComm (step92Split_of h34 h311a h311bComm h311bCard))
    (step94ConjV_of h34 h311a h311bComm)
    (step94CNAll_of_gen_notQB h34 h311a h311bComm h311bCard hGen hNotQB)

end CFSG.RankThree.GF2n.Stroth80
