module

public import Certificates.Data.RouteP.Objects
import Certificates.Kernel.RouteP.Obj.Glue

public section

open CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model.Native

namespace Certificates

open CertificateChecks

open CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model.Native in
theorem certificate450215 : objOK () = true :=
  KernelRouteP.objOKAt_of KernelRouteP.mTabs_O KernelRouteP.mTabs_P

end Certificates
