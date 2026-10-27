module

public import CFSG.RankThree.PartOne.KF.F122PSLTwo
public import CFSG.RankThree.PartOne.KF.F122PSL
public import CFSG.RankThree.PartOne.KF.F122PSUSplit
public import CFSG.RankThree.PartOne.KF.F122PSUFive
public import CFSG.RankThree.PartOne.KF.F122G2
public import CFSG.RankThree.PartOne.KF.F122D4
public import CFSG.RankThree.PartOne.KF.F122F4

public section

namespace CFSG.RankThree.PartOne

theorem kf122_of_classify
    (hc : KF123Classify) : KF122 := by
  refine kf122_of_rows hc kf122PSLTwo_holds fun r h1 h12 h11 => ?_
  interval_cases r
  · exact kf122Row1_holds.toW
  · exact kf122Row2_holds.toW
  · exact kf122Row3_holds.toW
  · exact kf122Row4_holds.toW
  · exact kf122Row5_holds.toW
  · exact kf122Row6_holds.toW
  · exact kf122Row7_holds.toW
  · exact kf122Row8_holds.toW
  · exact kf122Row9_holds.toW
  · exact kf122Row10_holds.toW
  · exact absurd rfl h11
  · exact kf122RowW12_holds

end CFSG.RankThree.PartOne
