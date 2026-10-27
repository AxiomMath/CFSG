
module


import Certificates.Kernel.Sporadic.LyBr.Rels
public import CFSG.Sporadic.Ly.Setup
public import Certificates.Certificate9120

public section

namespace Certificates

open CertificateChecks

open TauCeti in
theorem certificate9213 : ∃ φ : Sporadic.Lyons.presentation.Group →* GL (Fin 111) (ZMod 5),
    ∀ g : GL (Fin 111) (ZMod 5), g.val = CFSG.Sporadic.Ly.mA ∨ g.val = CFSG.Sporadic.Ly.mB →
      g ∈ φ.range := KernelSpor.LyRels.le_range

end Certificates
