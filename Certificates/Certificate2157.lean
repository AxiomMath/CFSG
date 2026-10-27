
module

public import Certificates.Certificate2157Base

public import CFSG.Sporadic.Schreier.Co3OrbitZCheckInputs
public meta import CFSG.Sporadic.Schreier.Co3Cert
public meta import Certificates.Data.CFSGNative.Co3Schreier.Orbit
import Certificates.Kernel.SporSch.Co3.OrbitZP
import CFSG.Certificates.Kernel.Spor.BindList
import CFSG.Certificates.Kernel.Spor.RawOrbGrp

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Sporadic CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Co3 CFSG.Certificates.Native in
open CFSG.Sporadic.Schreier.Co3.Native in
theorem certificate2157 : translatesOK co3OrigArrs co3IzNat co3OrbitZ.1 co3OrbitZ.2.1 co3OrbitZ.2.2 = true ∧
    keysSortedOK co3OrbitZ.1 = true ∧ co3OrbitZ.1.size = 170775 := KernelSporSch.Co3OrbZP.facts

end Certificates
