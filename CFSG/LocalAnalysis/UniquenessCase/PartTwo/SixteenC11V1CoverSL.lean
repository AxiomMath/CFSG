module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11V1Restrict
public import CFSG.Quasithin.H13.VolII16SLNat

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.JonesParshall

theorem s16c11_v1_cover_sl {m : ℕ} (hm : m = 4 ∨ m = 5)
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2) :
    S16C11V1ModelCover (FFModel.nat (StatedSL m K)) := by
  intro W _ _ hW2 H Z hZ hcomm h
  rcases hm with rfl | rfl
  · exact CFSG.Quasithin.H13.VolI.natSL_eq_bot (n := 4) Z1A_eq_B1A_four hK hW2 hZ hcomm h
  · exact CFSG.Quasithin.H13.VolI.natSL_eq_bot (n := 5) Z1A_eq_B1A_five hK hW2 hZ hcomm h

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
