module

public import CFSG.GF2Type.Smith1979.IdxFourModelBasic
public import CFSG.GF2Type.Smith1979.IdxFourModelData
public import CFSG.GF2Type.Smith1979.IdxFourModelE0Inputs
import Certificates.Kernel.IdxFour.Sift

public section

namespace Certificates

open CFSG.GF2Type.Smith1979.GammaU CFSG.GF2Type.Smith1979.IdxFour in
theorem certificate17605 : Viol.genGrp pGens ≤ E0 ∧ Viol.genGrp E0Chk.sGensE0 ≤ E0 ∧ s12e ∉ E0 :=
  CFSG.KD.IF4R.sift17605

end Certificates
