
module

public import Certificates.Certificate2320Base
public import CFSG.Sporadic.ThSchreier.PlaneFactsBase
public meta import CFSG.Sporadic.ThSchreier.UASpaceBase
import Certificates.Kernel.SporSch.Th.Plane2320Base

public import CFSG.Sporadic.ThSchreier.OrbitCheck819Base
public import CFSG.Sporadic.ThSchreier.PlaneFactsBase1
public meta import CFSG.Sporadic.ThSchreier.TransporterBase
public meta import CFSG.Sporadic.ThSchreier.UASpaceBase1
import Certificates.Kernel.SporSch.Th.Plane2320

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Sporadic CFSG.Sporadic.ThSchreier CFSG.Sporadic.Th CFSG.Sporadic.Th.Native in
open CFSG.Sporadic.Th.Max3 Pointwise in
theorem certificate2320 : inUA starKey.u = true ∧ inUA starKey.v = true := KernelSporSch.ThPlane.facts

end Certificates
