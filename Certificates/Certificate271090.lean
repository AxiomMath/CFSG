module

public import Certificates.Data.RouteCWit
import Certificates.Kernel.RouteCK.Checks
import CFSG.Certificates.Kernel.RouteCKSound

public section

open CFSG.CGT.PushingUpLit.CGT6.RouteC CFSG.Certificates.Kernel.RouteCK
  Certificates.Kernel.RouteCK

namespace Certificates

open CFSG.CGT.PushingUpLit.CGT6.RouteC in
theorem certificate271090 : routeCCheck = true := by
  simp only [routeCCheck, Bool.and_eq_true]
  exact ⟨⟨check_of_checkK _ _ _ chRC4, check_of_checkK _ _ _ chRC5⟩, check_of_checkK _ _ _ chRC6⟩

end Certificates
