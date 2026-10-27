module

public import CFSG.RankThree.PartTwo.Sec13.K135MultPrime
public import CFSG.RankThree.PartOne.N143.SectionListSporadicC
public import CFSG.LocalAnalysis.ComponentClassification.GoldschmidtTDGriess

public section

namespace CFSG.RankThree.PartTwo.Sec13.F135Last

theorem kFactMultPrime_holds :
    KFactMultPrime :=
  kFactMultPrime_of_inputs CFSG.ComponentClassification.TBLit.griessMultipliersAllModels_holds
    fun {s} hs {M} _ _ hM e {ℓ} hℓ h7 =>
      CFSG.RankThree.PartOne.N143.sporadic_no_seven_center hs hM e hℓ h7

end CFSG.RankThree.PartTwo.Sec13.F135Last
