module

public import CFSG.LocalAnalysis.UniquenessCase.UC22Main22
public import CFSG.LocalAnalysis.UniquenessCase.UC22P20x

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22.Ext

structure Global22i : Prop extends Global22e where
  griess : CFSG.Open.GriessAllModelsStatement
  nativeGriess : uc22p20rNativeGriess
  exclRes : uc22p20vExclRes
  twoRes : uc22p20vTwoRes
  diagram : uc22p20uDiagramInput

section Chain

variable {G : Type} [Group G] [Finite G]

theorem Global22i.toGlobal22h (hG : Global22i) : Global22h where
  toGlobal22e := hG.toGlobal22e
  griess := hG.griess
  nativeGriess := hG.nativeGriess
  excl := uc22p20x_excl_of_res hG.griess hG.nativeGriess hG.exclRes
  two := uc22p20x_two_of_res hG.griess hG.nativeGriess hG.twoRes
  diagram := hG.diagram

end Chain

end CFSG.LocalAnalysis.UniquenessCase.UC22
