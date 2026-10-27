
module

public import CFSG.GF2Type.Smith1979.IdxFourModelOrbitInputs
import Certificates.Kernel.IdxFour.Omega

public section

namespace Certificates

open CFSG.GF2Type.Smith1979.GammaU CFSG.GF2Type.Smith1979.IdxFour in
theorem certificate17606 : ∀ v : V12, Orb.inOmegab (codeOf v) = true →
    ∃ U ∈ Viol.genGrp pGens, U (vecOf 12) = v :=
  CFSG.KD.IF4W.exists_pGens_of_inOmegab

end Certificates
