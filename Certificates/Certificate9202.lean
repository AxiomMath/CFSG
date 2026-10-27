module

import Certificates.Kernel.Sporadic.Co1.Rels
public import CFSG.Sporadic.HS.Group
public import Certificates.Certificate9100
public import Certificates.Data.CFSGNative.Co1.Data

public section

namespace Certificates

open CertificateChecks

open CFSG.Sporadic.SmallF2 TauCeti in
theorem certificate9202 : ∃ φ : Sporadic.co1Presentation.Group →*
      GL (Fin (CFSG.Sporadic.Co1.Native.co1Data ()).d) (ZMod 2),
    J CFSG.Sporadic.Co1.Native.co1Data ≤ φ.range := KernelSpor.Co1Rels.le_range

end Certificates
