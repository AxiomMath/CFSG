module

public import CFSG.RankThree.PartOne.CTP.StrongPAssembly
public import CFSG.RankThree.PartOne.Census3.Assembly

public section

namespace CFSG.RankThree.PartOne.CTP

theorem threeCatalog_of_spin
    (hspin : Census3.SpinRankFour) (hB : Census3.RankFourBabyMonster) : ThreeCatalog :=
  fun G _ _ hhyp => by
    have := hhyp.isSimpleGroup
    exact Census3.theorem_three_catalog_of_spin hspin hB G hhyp.nonabelian hhyp.kGroup
      hhyp.twoLocalOddRank_le

end CFSG.RankThree.PartOne.CTP
