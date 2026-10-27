module

public import CFSG.RankThree.PartTwo.Sec19.SimsSolEvenYamakiExists
public import CFSG.RankThree.PartTwo.Sec19.SimsSolEvenYamakiRec

public section

namespace CFSG.RankThree.PartTwo.Sec19.SolEven

theorem yamakiSp62CharTwo_holds :
    YamakiSp62CharTwo :=
  YamakiRec.yamakiSp62CharTwo_of_fusionOut Yamaki.exists_fusionOut

end CFSG.RankThree.PartTwo.Sec19.SolEven
