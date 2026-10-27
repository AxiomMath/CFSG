module

public import CFSG.GF2Type.Smith1979.GammaU.CensusDefs
import Certificates.Kernel.GammaU.PairBridge
public import CFSG.GF2Type.Smith1979.GammaU.FrameLemma

public section

namespace Certificates

open CFSG.GF2Type.Smith1979.GammaU.StepA in
theorem certificate16968 : ∀ i, i = 0 ∨ i = 1 → PairFacts i := CFSG.KD.GUBB.pairFacts

end Certificates
