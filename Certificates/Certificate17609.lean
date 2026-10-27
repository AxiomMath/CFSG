module

public import CFSG.GF2Type.Smith1979.IdxFourModelDefs
public import CFSG.GF2Type.Smith1979.IdxFourModelData
import Certificates.Kernel.IdxFour.Sift

public section

namespace Certificates

open CFSG.GF2Type.Smith1979.GammaU CFSG.GF2Type.Smith1979.IdxFour in
theorem certificate17609 : Viol.genGrp sGens ≤ M0 ∧ Viol.genGrp lbarGens ≤ M0 :=
  CFSG.KD.IF4R.sift17609

end Certificates
