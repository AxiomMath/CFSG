module

public import CFSG.RankThree.PartTwo.Sec21.FF79Lemma42NMain
public import CFSG.RankThree.PartTwo.Sec21.FF79Lemma42NAb
public import CFSG.RankThree.PartTwo.Sec21.FF79Lemma42NNabT
public import CFSG.RankThree.PartTwo.KFacts.KS44Sz

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF79

open CFSG.RankThree.PartTwo.KFacts (KPSz kpSz)

theorem ff79LemmaN_of_kpSz (hSz : KPSz) : FF79LemmaN :=
  ff79LemmaN_of_bases (fun _ _ _ _ _ _ h hab hmin => LemmaN.nBase_abelian h hab hmin)
    (LemmaN.nBase_nab_general hSz)

theorem ff79LemmaN_holds
    : FF79LemmaN :=
  ff79LemmaN_of_kpSz kpSz

end CFSG.RankThree.PartTwo.Sec21.FF79
