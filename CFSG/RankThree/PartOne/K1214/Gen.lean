module

public import CFSG.RankThree.PartOne.K1214.Frame

public section

namespace CFSG.RankThree.PartOne.K1214

theorem kf1214Gen_of_h112 (h112 : InSec11Two) : KF1214Gen := by
  intro G _ _ p A c L E ctx b K I X P Q hL hC hF
  exact exists_f h112 ctx hL hC hF

end CFSG.RankThree.PartOne.K1214
