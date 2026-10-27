module

public import CFSG.Sporadic.Schreier.Co1OddACCheckInputs
public meta import CFSG.Sporadic.Schreier.Co1OddData
public meta import CFSG.Sporadic.Schreier.Co1StabCheck
public meta import CFSG.Sporadic.Schreier.Co1StabData
public meta import CFSG.Sporadic.Schreier.Co1OrbEnumCheck
public meta import CFSG.Sporadic.Schreier.Co1FullOrbCheck
public meta import CFSG.Sporadic.Schreier.Co1ThreeLocal
public meta import CFSG.Sporadic.Co1.Module.InvData
public meta import CFSG.Sporadic.Co1.Module.Forms
public meta import CFSG.Sporadic.Co1.Module.Orbits
public meta import Certificates.Data.CFSGNative.Co1Schreier.Base
public meta import Certificates.Data.CFSGNative.Co1.Data
public meta import Certificates.Data.CFSGNative.Co1.Odd
public meta import Certificates.Data.CFSGNative.Co1.Involutions
public meta import Certificates.Data.CFSGNative.HS.SmallF2
public meta import Certificates.Data.CFSGNative.Th.Tables
public meta import Certificates.Data.CFSGNative.Th.Orbit
import Certificates.Kernel.Co1Odd.Bridge2142

public section

namespace Certificates

open CFSG CFSG.Sporadic CFSG.Sporadic.Co1Schreier in
theorem certificate2142 : (Native.oddACCheckOf Native.oddACRegs = true)
    ∧ (Native.oddACCountsOf Native.oddACRegs = true)
    ∧ (Native.oddACXOf (Native.fullOrb 2) Native.oddACRegs = true) := CertificateChecks.KernelCo1Odd.facts2142

end Certificates
