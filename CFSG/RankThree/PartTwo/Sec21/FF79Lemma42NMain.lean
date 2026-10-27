module

public import CFSG.RankThree.PartTwo.Sec21.FF79Lemma42Defs
public import CFSG.RankThree.PartTwo.Sec21.FF79Lemma42NInd

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF79

open CFSG.RankThree.PartTwo.Sec21.FF79.LemmaN

theorem ff79LemmaN_of_bases (hA : NBaseAb) (hN : NBaseNab) : FF79LemmaN :=
  fun _ _ _ _ _ _ hk hiso hnor hcop hb hord hcent =>
    lemmaN_of_bases hA hN ⟨hk, hiso, hnor, hcop, hb, hord, hcent⟩

end CFSG.RankThree.PartTwo.Sec21.FF79
