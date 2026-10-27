module

public import CFSG.Quasithin.Background.C129NativeLight
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.TopFinal
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1J4OutFinal

public section

namespace CFSG.Quasithin

open CFSG.QuasithinUnique

theorem asc129StatementUsed_of_native
    (hB113 : Bridge.AsB113With CFSG.SectionRank.IsKGroupCat) :
    ∀ (G : Type) [Group G] [Finite G], ASC129StatementUsed G :=
  fun G _ _ => asc129StatementUsed_of_minParabolicBlocks
    (Setup.Top.minParabolicBlocks_final Setup.X1.sporadicExclusion_J4_proved) hB113 G

end CFSG.Quasithin
