module

public import CFSG.GF2Type.Smith1979.GammaU.SylowFacts
import Certificates.Kernel.GammaU.SylowFacts

public section

namespace Certificates

open CFSG.GF2Type.Smith1979.GammaU.SigmaP in
theorem certificate16973 : ∀ i, i = 0 ∨ i = 1 → SylowFacts i := CFSG.KD.GUY.sylowFacts

end Certificates
