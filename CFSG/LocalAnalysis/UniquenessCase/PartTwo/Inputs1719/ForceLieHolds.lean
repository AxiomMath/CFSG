module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.ForceLieLinear
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.ForceLieOmega
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.ForceLieU33
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.ForceLieSymplectic
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.ForceLieCases
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.ForceLieSmall
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.ForceLieL52
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.KFact1920ForceShape

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719


theorem k_19_20_forceLie_holds : K_19_20_forceLie := by
  intro X _ _ Q _ Y hq h2 hQ ⟨hL, hlist, hpar⟩ hT1 hT2 hT3
  rcases forceLie_cases hL hlist with h | h | h | h | h | h | h | h | h | h
  · exact lieModel_of_cover_L32 hq h2 hQ h
  · exact (false_of_cover_L42 hq h2 hQ h hpar hT2).elim
  · exact (false_of_cover_L52 hq hQ h hpar hT2 hT3).elim
  · exact (not_cubesCommute_of_cover hQ (forceRealPair_of_lieModel_PSL_six h) hT1).elim
  · exact (not_cubesCommute_of_cover hQ (forceRealPair_of_lieModel_PSL_seven h) hT1).elim
  · exact (not_cubesCommute_of_cover hQ (forceRealPair_of_lieModel_PSU_four h) hT1).elim
  · exact (not_cubesCommute_of_cover hQ (forceRealPair_of_lieModel_PSp_three h) hT1).elim
  · exact (not_cubesCommute_of_cover hQ (forceRealPair_of_lieModel_POmegaMinus_four h) hT1).elim
  · exact (false_of_cover_A6 hq h2 hQ h hpar hT1 hT2).elim
  · exact (not_cubesCommute_of_cover hQ (forceRealPair_of_lieModel_PSU_three_three h) hT1).elim

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
