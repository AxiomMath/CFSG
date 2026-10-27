
module


import Certificates.Kernel.GammaU.SigmaFacts
public import CFSG.GF2Type.Smith1979.GammaU.SigmaFacts

public section

namespace Certificates

open CFSG.GF2Type.Smith1979.GammaU.SigmaP in
theorem certificate16981 : ∀ i, i = 0 ∨ i = 1 → SigmaFacts i := CFSG.KD.GUS.sigmaFacts

end Certificates
