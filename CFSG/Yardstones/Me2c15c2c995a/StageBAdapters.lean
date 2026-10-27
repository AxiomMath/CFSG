module

public import CFSG.Yardstones.Me2c15c2c995a.Definitions

public section

namespace CFSG.Yardstones.Me2c15c2c995a

theorem ascEighteenTwentyFour_of_conditional
    (h16 : AscSixteenSixtyNine) (h18 : AscEighteenTwentyFourConditional) :
    AscEighteenTwentyFour := by
  intro G _ _ hStanding hUC S hMS V₀ V h125
  apply lt_of_not_ge
  intro hsmall
  exact h18 G hStanding hUC S hMS V₀ V h125 hsmall
    (h16 G hStanding hUC S hMS V₀ V h125 (hsmall.trans (by decide)))

theorem ascSectionNineteen_of_conditional
    (h16 : AscSixteenSixtyNine) (h18 : AscEighteenTwentyFour)
    (h19 : AscSectionNineteenConditional) : AscSectionNineteen := by
  intro G _ _ hStanding hUC S hMS V₀ V h125
  exact h19 G hStanding hUC S hMS V₀ V h125
    (h18 G hStanding hUC S hMS V₀ V h125)
    (fun hsmall => h16 G hStanding hUC S hMS V₀ V h125 hsmall)

end CFSG.Yardstones.Me2c15c2c995a
