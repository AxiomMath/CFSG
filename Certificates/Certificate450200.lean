module

public import Certificates.Data.RouteP.Bridge
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.Fi24ThreeCoverInputs
import Certificates.Kernel.RouteP.Bridge.Glue
import Certificates.Kernel.RouteP.Link.Glue

public section

open CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model.Native
  CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator

namespace Certificates

open CertificateChecks

open CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model.Native
  CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator in
theorem certificate450200 : bridgeOK (wsQ.map fun w => w.map fun l =>
    if l.2 then (l.1.val : Int) + 1 else -((l.1.val : Int) + 1)) = true :=
  KernelRouteP.bridgeOKAt_of KernelRouteP.mTabs_P

end Certificates
