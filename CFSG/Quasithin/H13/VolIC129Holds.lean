module

public import CFSG.Quasithin.H13.VolIC129
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B113Final
public import CFSG.Quasithin.Background.B15P4Layer2Final
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.TopFinal

public section

namespace CFSG.Quasithin.H13.VolI

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

theorem asc129Statement_holds
    : ∀ (G : Type) [Group G] [Finite G], ASC129Statement G :=
  asc129Statement_of_minParabolicBlocks
    (Setup.Top.minParabolicBlocks_final Setup.X1.sporadicExclusion_J4_proved)
    (Bridge.asB113_of_timmesfeld CFSG.Quasithin.B15P4.asB15Part4)

end CFSG.Quasithin.H13.VolI
