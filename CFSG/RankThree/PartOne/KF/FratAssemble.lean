module

public import CFSG.RankThree.PartOne.KF.FratRow1
public import CFSG.RankThree.PartOne.KF.FratRow9

public section

namespace CFSG.RankThree.PartOne

theorem kf1215Frat_of_rows
    (hGA : CFSG.Open.GriessAllModelsStatement)
    (hU5 : KF1214U5) (h2 : KF1215Scalar 2) (h3 : KF1215Scalar 3) (h4 : KF1215Scalar 4)
    (h5 : KF1215Scalar 5) (h6 : KF1215Scalar 6) (h8 : KF1215Scalar 8)
    (h10 : KF1215Scalar 10) : KF1215Frat := by
  refine kf1215Frat_of_scalar fun r hr1 hr12 hr7 hr11 => ?_
  interval_cases r
  · exact kf1215Scalar1
  · exact h2
  · exact h3
  · exact h4
  · exact h5
  · exact h6
  · exact absurd rfl hr7
  · exact h8
  · exact kf1215Scalar9_of_multipliers hGA
  · exact h10
  · exact absurd rfl hr11
  · intro G _ _ p A c L E ctx hmodel
    exact absurd hmodel (hU5 G p A c L E ctx)

end CFSG.RankThree.PartOne
