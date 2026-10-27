module

public import Certificates.Data.RouteP.Y332
public import CFSG.Sporadic.Recognition.Fi22MultiplierInputs
import Certificates.Kernel.RouteP.Y332.Facts

public section

open CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model.Native CFSG.YGroups
  CFSG.Sporadic.Recognition.Fi22Multiplier

namespace Certificates

open CertificateChecks

open CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model.Native CFSG.YGroups
  CFSG.Sporadic.Recognition.Fi22Multiplier in
theorem certificate450250 : y332OK ((yRels 3 3 2 ++ [f332Word]).map fun w => w.map fun (c : Nat) => (c : Int) + 1) =
    true :=
  KernelRouteP.y332OKAt_of KernelRouteP.mTabs_Y

end Certificates
