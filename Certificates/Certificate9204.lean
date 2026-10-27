module

import Certificates.Kernel.Sporadic.Co3.Rels
public import CFSG.Sporadic.HS.Group
public import Certificates.Data.CFSGNative.Co3.Data
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Conway.Three

public section

namespace Certificates

open CertificateChecks

open CFSG.Sporadic.SmallF2 TauCeti in
theorem certificate9204 : ∃ φ : Sporadic.co3Presentation.Group →*
      GL (Fin (CFSG.Sporadic.Co3.Native.co3Data ()).d) (ZMod 2),
    J CFSG.Sporadic.Co3.Native.co3Data ≤ φ.range := KernelSpor.Co3Rels.le_range

end Certificates
