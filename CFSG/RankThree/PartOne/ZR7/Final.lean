module

public import CFSG.RankThree.PartOne.ZR7.Inst
public import CFSG.RankThree.PartOne.K1214.ZRows

public section

namespace CFSG.RankThree.PartOne.ZR7

open CFSG CFSG.Assembly CFSG.RankThree CFSG.RankThree.GroupTheory CFSG.Blueprint
open CFSG.RankThree.PartOne.K1214
open CFSG.RankThree.PartOne.S12K (LieRigidity3)

theorem kf1214ZRow7_holds
    (h112 : InSec11Two) (hRig : LieRigidity3) (hKR : KFixedRes) (hU5 : KF1214U5)
    (hFix : FieldFixedPElements) : KF1214ZRow 7 :=
  fun _ _ _ _ _ _ _ _ ctx h7 _ _ _ _ _ _ hL hC hF hgen =>
    zr7_clauses h112 hRig hKR hU5 hFix ctx h7 hL hC hF hgen

end CFSG.RankThree.PartOne.ZR7
