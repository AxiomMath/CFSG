module

public import CFSG.RankThree.PartOne.KF.F132Row2Types
public import CFSG.RankThree.PartOne.KF.F132Row3Types
public import CFSG.RankThree.PartOne.KF.F132F4Bridge
public import CFSG.RankThree.PartOne.KF.F132Row7Frame
public import CFSG.RankThree.PartOne.S13K.Assembly

public section

namespace CFSG.RankThree.PartOne

open CFSG.RankThree.PartOne.S13K

theorem kf132Types_ne8
    (hGA : CFSG.Open.GriessAllModelsStatement)
    (hECS : ExceptionalCenterSmallPrimes) :
    ∀ r : ℕ, 1 ≤ r → r ≤ 12 → r ≠ 8 → KF132Types r := by
  intro r hr1 hr12 hr8
  interval_cases r
  · exact kf132Types_of_at (by norm_num) (by norm_num) (by norm_num) (kf132At_row1 hGA)
  · exact kf132Types_row2 hGA hECS
  · exact kf132Types_row3 hGA hECS
  · exact kf132Types_row4_of_hGA hGA
  · exact kf132Types_row5 hGA
  · exact kf132Types_row6 hGA
  · exact kf132Types_row7 hGA
  · exact absurd rfl hr8
  · exact kf132Types_row9 hGA
  · exact kf132Types_row10 hGA
  · exact kf132Types_of_at (by norm_num) (by norm_num) (by norm_num) (kf132At_row11 hGA)
  · exact kf132Types_of_at (by norm_num) (by norm_num) (by norm_num) (kf132At_row12 hGA)

end CFSG.RankThree.PartOne
