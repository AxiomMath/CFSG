module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.WeakClosureNineBModel
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.WeakClosureNineBMap
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.WeakClosureNineBRedDefs

public section

namespace CFSG.LocalAnalysis.WeakClosure81.NGM

theorem nGFactsOfModel_holds : NGIdent → NGModelFacts → NGFacts := by
  intro hI hM X _ _ L1b L2b Tb h1 h2 h3 h4 h5 h6 h7 h8 h9
  obtain ⟨i, e, hL1, hL2, hT⟩ := hI X L1b L2b Tb h1 h2 h3 h4 h5 h6 h7 h8 h9
  have hm : ModelFacts915 i := hM i
  rw [ModelFacts915, ← hL1, ← hL2, ← hT] at hm
  exact NineFifteenBarFacts.of_map_equiv e hm

end CFSG.LocalAnalysis.WeakClosure81.NGM
