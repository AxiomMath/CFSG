module

public import Certificates.Data.RouteP.Cocode
import Certificates.Kernel.RouteP.Obj.Run

public section

open CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model.Native

namespace Certificates

open CertificateChecks

open CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model.Native in
theorem certificate450260 : cocodeOK () = true :=
  KernelRouteP.cocodeOKAt_of KernelRouteP.objRun_rep

end Certificates
