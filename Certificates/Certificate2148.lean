
module

public import Certificates.Certificate2148Base

public import CFSG.Sporadic.Schreier.Co1StabCheckInputs
public meta import CFSG.Sporadic.Schreier.Co1OrbEnumCheck
public meta import CFSG.Sporadic.Schreier.Co1StabData
public meta import CFSG.Sporadic.Schreier.Co1FullOrbCheckBase
public meta import CFSG.Sporadic.Schreier.Co1ThreeLocal
public meta import Certificates.Data.CFSGNative.Co1Schreier.Base
public meta import Certificates.Data.CFSGNative.Co1.Data
public meta import Certificates.Data.CFSGNative.HS.SmallF2
public meta import Certificates.Data.CFSGNative.Th.Tables
public meta import Certificates.Data.CFSGNative.Th.Orbit
import Certificates.Kernel.SporSch.Co1.Stab2148Proved

public section

namespace Certificates

open CertificateChecks

open CertificateChecks.KernelSporSch.Co1Stab2148 in
open CFSG CFSG.Sporadic CFSG.Sporadic.Co1Schreier in
theorem certificate2148 : (Native.stabOrbCheck = true)
    ∧ (Native.stabXCheck = true)
    ∧ (Native.witCheck = true)
    ∧ (Native.fixCheck = true)
    ∧ (Native.memCheck = true) :=
  ⟨orb_proved, x_proved, wit, fix, mem_proved⟩

end Certificates
