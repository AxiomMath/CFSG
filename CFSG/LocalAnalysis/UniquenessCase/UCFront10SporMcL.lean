module

public import CFSG.LocalAnalysis.UniquenessCase.UCFront10SporDc2
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatMcLDc2

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.F10

open CFSG.QuasithinUnique.Ch1.SporLat.McLK CFSG.Sporadic.Schreier in
theorem k105SporAt_McL :
    K105SporAt .McL := by
  have e : CFSG.Blueprint.NativeSporadic.Carrier .McL ≃* ↥mclP := mclPermEquiv
  exact k105SporAt_of_dc2 (n := 275) CFSG.KD.McLDc2.C rfl CFSG.KD.McLDc2.D els rfl hL card_S hN
    hodd hsep facts.1 e

end CFSG.LocalAnalysis.UniquenessCase.UC22.F10
