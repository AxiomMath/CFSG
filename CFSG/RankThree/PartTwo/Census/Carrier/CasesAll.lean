module

public import CFSG.RankThree.PartTwo.Census.Carrier.CasesSpin
public import CFSG.RankThree.PartTwo.Census.Carrier.G2Even
public import CFSG.RankThree.PartTwo.Census.Carrier.D4Even
public import CFSG.RankThree.PartTwo.Census.Carrier.ReeF4Bridge

public section

namespace CFSG.RankThree.PartTwo.Census

theorem carrierCases433 : CarrierCases433 :=
  carrierCases433_of_spin excluded433_G2_even excluded433_trialityD4_even excluded433_reeF4
    excluded433_tits

end CFSG.RankThree.PartTwo.Census
