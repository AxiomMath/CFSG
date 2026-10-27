module

public import CFSG.Sporadic.Schreier.Co1AutCheckInputs
public meta import CFSG.Sporadic.Schreier.Co1StabCheck
public meta import CFSG.Sporadic.Schreier.Co1ChainCheck
public meta import CFSG.Sporadic.Schreier.Co1AutData
public meta import CFSG.Sporadic.Schreier.Co1StabData
public meta import CFSG.Sporadic.Schreier.Co1OrbEnumCheck
public meta import CFSG.Sporadic.Schreier.Co1FullOrbCheck
public meta import CFSG.Sporadic.Schreier.Co1ThreeLocal
public meta import Certificates.Data.CFSGNative.Co1Schreier.Base
public meta import Certificates.Data.CFSGNative.Co1.Data
public meta import Certificates.Data.CFSGNative.HS.SmallF2
public meta import Certificates.Data.CFSGNative.Th.Tables
public meta import Certificates.Data.CFSGNative.Th.Orbit
import Certificates.Kernel.SporSch.Co1.Aut

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Sporadic CFSG.Sporadic.Co1Schreier in
theorem certificate2130 : (Native.stabTowerCheck = true)
    ∧ (Native.nonlinCheck = true) :=
  ⟨KernelSporSch.Co1Aut.tower, KernelSporSch.Co1Aut.nonlin⟩

end Certificates
