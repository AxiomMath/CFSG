module

public import CFSG.GF2Type.Smith1979.GammaU.FrameCensusDefs
import Certificates.Kernel.GammaU.FrameC
public import CFSG.GF2Type.Smith1979.GammaU.FrameLemma

public section

namespace Certificates

theorem certificate16982 : ∀ i, i = 0 ∨ i = 1 → CFSG.GF2Type.Smith1979.GammaU.StepA.FrameCensusFacts i := CFSG.KD.GUFC.frameCensusFacts

end Certificates
