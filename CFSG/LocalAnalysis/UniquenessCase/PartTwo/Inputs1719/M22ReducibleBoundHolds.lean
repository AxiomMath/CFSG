module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.M22CoverPoints
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.M22ReducibleBBound
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.M22ReducibleMBound

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Open CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo

theorem k_M22ReducibleBound_holds :
    K_M22ReducibleBound := by
  intro W _ _ hw Y L hLY hN hSpor hfix hss hnirr
  have hb := bParam_le_three_of_M22 (W := W) (Y := Y) (L := L) hw hLY hN hSpor hfix
  have hm := six_le_mParam_of_M22 (W := W) (Y := Y) (L := L) hw hLY hN hSpor hfix hss hnirr
  omega

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
