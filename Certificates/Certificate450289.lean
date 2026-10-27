module

public import Certificates.Data.RouteP.Q0Planes
public import Certificates.Data.RouteP.Rigid
import Certificates.Kernel.RouteP.Rigid.Proof

public section

namespace Certificates

open CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model.Native in
open CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Rigid.Native in
theorem certificate450289 : rigidOK 891 (planeDTabs ()) (planeInterCount (planeXData ())) = true :=
  CertificateChecks.KernelRouteP.rigidOK_planeDTabs

end Certificates
