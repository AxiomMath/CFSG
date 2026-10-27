module

public import Certificates.Data.RouteP.QCent
import Certificates.Kernel.RouteP.QCent.Glue

public section

open CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model.Native

namespace Certificates

open CertificateChecks

open CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model.Native in
theorem certificate450290 : qcentOK () = true :=
  KernelRouteP.qcentOK_true

end Certificates
