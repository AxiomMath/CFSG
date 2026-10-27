module

public import CFSG.LocalAnalysis.StandardType.GGTwE6WeylTorusModelTransfer
public import CFSG.LocalAnalysis.StandardType.GGTwE6WeylTorusNoTransvection
public import CFSG.LocalAnalysis.StandardType.GGTwE6WeylTorusPackage

public section

namespace CFSG.StandardType

section Holds


theorem ggTwE6TorusModelInput_holds : GGTwE6TorusModelInput := by
  intro K _ _ n p hn hK hp hpn hp5
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hp2 : p ≠ 2 := by omega
  have hp3 : p ≠ 3 := by omega
  exact TwE6TB.ggTorusModelSCr_of_scWeylModel hp (TwE6Delta.center_recipeR_eq_bot hn hK)
    (TwE6Delta.ggOutdiagPrime_twE6 hn hK hp hp3) (TwE6Delta.ggCenterPrime_twE6 hn hK hp hp2 hp3)
    (TwE6TB.ggSCWeylModel_of_framePackage (r := 5) (by norm_num)
      (TwE6TB.ggTwE6FramePackage_recipeR hp5 hn hK hpn))

theorem ggTwE6NoTransvectionInput_holds : GGTwE6NoTransvectionInput := by
  intro K _ _ n p hn hK hp hpn hp5
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hp2 : p ≠ 2 := by omega
  have hp3 : p ≠ 3 := by omega
  exact TwE6TB.ggNoTransvectionSCr_of_framePackage hp2 hp3 (r := 5) (by norm_num)
    (TwE6Delta.center_recipeR_eq_bot hn hK) (TwE6Delta.ggOutdiagPrime_twE6 hn hK hp hp3)
    (TwE6Delta.ggCenterPrime_twE6 hn hK hp hp2 hp3) (TwE6TB.ggTwE6FramePackage_recipeR hp5 hn hK hpn)

end Holds

end CFSG.StandardType
