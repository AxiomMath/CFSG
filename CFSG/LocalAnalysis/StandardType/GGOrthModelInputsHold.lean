module

public import CFSG.LocalAnalysis.StandardType.GGOrthModelInputs
public import CFSG.LocalAnalysis.StandardType.GGOrthRk1Fork
public import CFSG.LocalAnalysis.StandardType.GGOrthRk1Gen
public import CFSG.LocalAnalysis.StandardType.GGOrthRk1Pair

public section

namespace CFSG.StandardType

namespace OrthTorus

theorem orthRankOneModelInput_holds : OrthRankOneModelInput := by
  intro K _ _ _ V _ _ _ Q p _ hp2 A hAΩ r Δ hr hq hfix
  exact tbjOm_rankOneModel hp2 hAΩ Δ hr hq hfix

theorem orthPairModelInput_holds : OrthPairModelInput := by
  intro K _ _ _ V _ _ _ Q p _ hp2 A hAΩ r Δ hr hpq hfix f hf K' _ _ _ hK' i j k hij hjk hik
  exact tbjOm_pair_model hp2 hAΩ Δ hr hpq hfix f hf K' hK' i j k hij hjk hik


theorem orthGenModelInput_holds : OrthGenModelInput := by
  intro hD K _ _ _ V _ _ _ Q p _ hp2 A hAΩ r Δ hr hq hpq hfix f hf K' _ _ _ hK' h2 h4 hUPlus hUMinus
  exact tbjOm_generation_model hD hp2 hAΩ Δ hr hq hpq hfix f hf K' hK' h2 h4 hUPlus hUMinus

end OrthTorus

end CFSG.StandardType

end
