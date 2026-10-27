module

public import Certificates.Data.RouteP.Q0Planes
import Certificates.Kernel.RouteP.Plane.Glue

public section

namespace Certificates

open CertificateChecks

open CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model.Native in
theorem certificate450285 : q0PlanesOK () = true :=
  KernelRouteP.q0PlanesOK_true

end Certificates
