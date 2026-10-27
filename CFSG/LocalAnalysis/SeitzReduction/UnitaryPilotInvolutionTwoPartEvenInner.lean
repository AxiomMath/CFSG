module

public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotInvolutionTwoPartEven
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14LUEven

public section

namespace CFSG.SeitzReduction.SymplecticPilot

theorem unitaryEvenInnerTwoPart_holds : UnitaryEvenInnerTwoPart :=
  fun _ _ _ h _ hn y hy => UnitaryPilot.le_factorization_card_centralizer_even h hn y hy

end CFSG.SeitzReduction.SymplecticPilot
