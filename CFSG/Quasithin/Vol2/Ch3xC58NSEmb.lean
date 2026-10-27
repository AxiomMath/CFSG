module

public import CFSG.Quasithin.Vol2.Ch3xC58NSEmbMain
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B113Final
public import CFSG.Quasithin.Background.B15P4Layer2Final
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.TopFinal
public import CFSG.Quasithin.Background.C129NativeLight

public section

namespace CFSG.Quasithin.C58NS

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

theorem embedLocal_holds
    : EmbedLocal :=
  embedLocal_of_b113 (Bridge.asB113_of_timmesfeld B15P4.asB15Part4) L246C127.altEvenExcluded
    (Setup.Top.minParabolicBlocks_final Setup.X1.sporadicExclusion_J4_proved)
    (fun _ _ _ => L238.altBlockStatementJCat_holds) C129Native.a38ForSQTKCat_proved

end CFSG.Quasithin.C58NS
