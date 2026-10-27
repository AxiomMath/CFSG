module

public import CFSG.GF2Type.Smith1979.IdxFourModelData
import Certificates.Kernel.IdxFour.SaChain
public import CFSG.GF2Type.Smith1979.GammaU.Violation

public section

namespace Certificates

open CFSG.GF2Type.Smith1979.GammaU CFSG.GF2Type.Smith1979.IdxFour in
theorem certificate17607 : 23040 ≤ Nat.card (Viol.genGrp sGens) :=
  CFSG.KD.IF4S.le_card_genGrp_sGens

end Certificates
