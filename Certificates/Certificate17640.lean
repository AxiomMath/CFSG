module

public import CFSG.GF2Type.Smith1979.IdxFourModelOrbitInputs
import Certificates.Kernel.IdxFour.OrbC

public section

namespace Certificates

open CFSG.GF2Type.Smith1979.GammaU CFSG.GF2Type.Smith1979.IdxFour in
theorem certificate17640 : ∀ v : V12, Orb.inO1701b (codeOf v) = true → f0 v (vecOf 3) = 0 →
    64 ≤ Set.ncard {u : V12 | ∃ U ∈ Viol.genGrp pGens, U v = u} :=
  CFSG.KD.IF4V.ncard_orbit_pGens

end Certificates
