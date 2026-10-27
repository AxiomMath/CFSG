module

public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallExcC5Node
public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallExcC5E7
public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallExcC5E8
public import CFSG.LocalAnalysis.StandardType.GGTableBExcTwoFusionE7
public import CFSG.LocalAnalysis.StandardType.GGTableBExcTwoFusionE8
public import CFSG.LocalAnalysis.StandardType.GGTableBExcTwoTBHalf

public section

namespace CFSG.StandardType.SmallExc

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.HardMathSupport.Timmesfeld.CrossChar
  TableBExcTwo TableBExcTwoFusion TableBExcTwoTB

section FinalE7


theorem ggE7TwoTorusNodeInput : GGE7TwoTorusNodeInput := by
  intro K _ _ _ hK A hA hcard x hxA hx1
  obtain ⟨_, hω, S, hS⟩ := exists_frameLang_of_perfect (Or.inl ⟨rfl, rfl⟩) frameE7
    frameE7_reflections hK (commutator_adjointGroup_E7_eq_top K)
  exact nodeCount_of_frameLang (Or.inl rfl) frameE7_parseval (by norm_num) hS hA hcard hxA hx1

theorem ggE7TwoNormSmallInput_holds : GGE7TwoNormSmallInput :=
  ggE7TwoNormSmallInput_of_nodes ggE7TwoSCToralInput_holds ggE7TwoTorusNodeInput

end FinalE7

section FinalE8


theorem ggE8TwoTorusNodeInput : GGE8TwoTorusNodeInput := by
  intro K _ _ _ hK A hA hcard x hxA hx1
  obtain ⟨_, hω, S, hS⟩ := exists_frameLang_of_perfect (Or.inr ⟨rfl, rfl⟩) frameE8
    frameE8_reflections hK (commutator_adjointGroup_E8_eq_top K)
  exact nodeCount_of_frameLang (Or.inr rfl) frameE8_parseval (by norm_num) hS hA hcard hxA hx1

theorem ggE8TwoNormSmallInput_holds : GGE8TwoNormSmallInput :=
  ggE8TwoNormSmallInput_of_nodes ggE8TwoSCToralInput_holds ggE8TwoTorusNodeInput

end FinalE8

end CFSG.StandardType.SmallExc

end
