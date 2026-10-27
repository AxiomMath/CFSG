
module

public import Certificates.Certificate2315Base
public meta import CFSG.Sporadic.ThSchreier.LocalOrbitBase
import Certificates.Kernel.SporSch.Th.Orb2315Base

public import CFSG.Sporadic.ThSchreier.OrbitCheck819Inputs
public meta import CFSG.Sporadic.ThSchreier.TransporterBase
public meta import CFSG.Sporadic.ThSchreier.LocalOrbitBase1
import Certificates.Kernel.SporSch.Th.Orb2315
import Certificates.Kernel.SporSch.Th.Plane2320

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Sporadic CFSG.Sporadic.ThSchreier CFSG.Sporadic.Th CFSG.Sporadic.Th.Native in
open CFSG.Sporadic.Th.Max3 in
theorem certificate2315 : orbitChecks orbTable = true := KernelSporSch.ThOrb.facts

end Certificates
