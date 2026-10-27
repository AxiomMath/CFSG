module

public import CFSG.LocalAnalysis.UniquenessCase.UCFront10SporDc2
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatSuzDc2

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.F10

open CFSG.QuasithinUnique.Ch1.SporLat.SuzK CFSG.Sporadic.SuzOddCore in
theorem k105SporAt_Suz :
    K105SporAt .Suz := by
  have e : CFSG.Blueprint.NativeSporadic.Carrier .Suz ≃* ↥suzP := suzEquivP
  exact k105SporAt_of_dc2 (n := 22880) CFSG.KD.SuzDc2.C rfl CFSG.KD.SuzDc2.D els rfl hL card_S hN
    hodd hsep facts.1 e

end CFSG.LocalAnalysis.UniquenessCase.UC22.F10
