module

public import CFSG.GF2Type.Smith1979.IdxFourModelBasic
public import CFSG.GF2Type.Smith1979.IdxFourModelData
public import CFSG.GF2Type.Smith1979.IdxFourModelSpec
import Certificates.Kernel.IdxFour.LbarFacts
public import Certificates.Certificate16982

public section

namespace Certificates

open CFSG.GF2Type.Smith1979.GammaU CFSG.GF2Type.Smith1979.IdxFour in
theorem certificate17610 : ∀ t ∈ Viol.genGrp lbarGens, t ≠ 1 → t * omegaE = omegaE * t →
    ModelInner (spanOf vtBasis) t :=
  CFSG.KD.IF4T.facts17610

end Certificates
