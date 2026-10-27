module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3L3MultB1ABA

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

theorem s16h_e3_irrSet_L3_card_eq_minLeftInv {W : Type} [CommGroup W] [Finite W]
    {L : Subgroup (MulAut W)} {U : Subgroup W} (hU : commSub (⊤ : Subgroup W) L = U)
    (C : s16h_L3Coord L U) :
    Nat.card ↥(irrSet L) =
      Nat.card {I : AddSubgroup (Matrix (Fin 3) (Fin 3) (ZMod 2)) // s16h_IsMinLeftInvMat I} := by
  obtain ⟨e⟩ := s16h_e3_irrSet_L3_equiv_minLeftInv hU C
  exact Nat.card_congr e

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
