module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.TopFinal
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1J4OutFinal

public section

namespace CFSG.Quasithin.R3c20

open CFSG.QuasithinUnique

theorem minParabolicBlocks_holds
    : MinParabolicBlocks :=
  Setup.Top.minParabolicBlocks_final Setup.X1.sporadicExclusion_J4_proved

end CFSG.Quasithin.R3c20
