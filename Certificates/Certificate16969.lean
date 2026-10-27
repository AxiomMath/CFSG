module

public import CFSG.GF2Type.Smith1979.GammaU.CensusDefs
import Certificates.Kernel.GammaU.TripleBridge
public import CFSG.GF2Type.Smith1979.GammaU.FrameLemma

public section

namespace Certificates

open CFSG.GF2Type.Smith1979.GammaU.StepA in
theorem certificate16969 : ∀ i, i = 0 ∨ i = 1 → TripleFacts i := CFSG.KD.GUBB.tripleFacts

end Certificates
