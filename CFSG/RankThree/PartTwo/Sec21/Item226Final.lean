module

public import CFSG.RankThree.PartTwo.Sec21.Item226
public import CFSG.RankThree.PartTwo.Sec21.Item223Of
public import CFSG.RankThree.PartTwo.Sec21.Item226Steps

public section

namespace CFSG.RankThree.PartTwo.Sec21

theorem rank3II_22_6_of_steps (h2115 : Item2115)
    (h2130 : Item2130) (h222 : Item222) (hP : Item223Print)
    (hKW : KOfWellDefinedAll) (hPhan : PhanChain) (hZ : CentralExtensionTrivial226)
    (hLR : LocalRankLowerBound226) : Item226 :=
  have h223 : Item223 := item223_of_print h2115 h222 hKW hP
  rank3II_22_6_of_item73 h2115 h2130 h222 h223 hKW hPhan
    (rank3II_22_6_centralReflection h222 h223) (rank3II_22_6_localSetS3 h2130 h222 h223 hKW)
    (rank3II_22_6_oThreeCentral h2130) hZ hLR

end CFSG.RankThree.PartTwo.Sec21
