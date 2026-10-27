module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3L3MultB1AB

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

public theorem s16h_e3_irrSet_L3_card_seven_of_coord {W : Type} [CommGroup W] [Finite W]
    {L : Subgroup (MulAut W)} {U : Subgroup W} (hU : commSub (⊤ : Subgroup W) L = U)
    (C : s16h_L3Coord L U) :
    Nat.card ↥(irrSet L) = 7 := by
  rw [s16h_e3_irrSet_L3_card_eq_minLeftInv hU C]
  exact s16h_e3_gl3_minimal_left_invariant_card

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
