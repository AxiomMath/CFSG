module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3MixedL3BA1AA
public import CFSG.Quasithin.H13.VolII16SLNat
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenFixHalfCover

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup

theorem s16h_e3_l3_three_ne_bot_boundCover {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2) :
    S16BoundCover (FFModel.nat (StatedSL 3 K)) 1 := by
  intro W _ _ hW2 H Z hZ hcomm hreal
  simpa using CFSG.Quasithin.H13.VolI.natSL_card_le (n := 3) s16h_l3_nat_Z1A_card
    hK hW2 hZ hcomm hreal

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
