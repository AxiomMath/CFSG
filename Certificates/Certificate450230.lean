module

public import Certificates.Data.RouteP.Geom
import Certificates.Kernel.RouteP.Geom.Dist

public section

namespace Certificates

open CertificateChecks

open CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Geom.Native in
theorem certificate450230 : geomOK () = true :=
  KernelRouteP.geomOK_true

end Certificates
