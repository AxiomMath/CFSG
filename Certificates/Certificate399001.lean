module

public import Certificates.Data.A6h2Swap
import Certificates.Kernel.A6h2Swap.Checks
import Certificates.Kernel.AE6F.Final
import CFSG.Certificates.Kernel.A6h2SwapSound

public section

namespace Certificates

open CertificateChecks

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CertificateChecks.KernelAE6F Certificates.AE6Model

private theorem prep_RG (c : Nat) :
    Orb.PRep 360 9 (RG.getD c (pidn 360 9)) ((curtisPerms ()).getD c 1) := by
  by_cases hl : c < 8
  · rw [getD_RG hl]
    exact prep_curtis hl
  · have e1 : (curtisPerms ()).getD c 1 = 1 := by
      rw [List.getD_eq_default]
      simp [curtisPerms]
      omega
    have e2 : RG.getD c (pidn 360 9) = pidn 360 9 := by
      rw [List.getD_eq_default]
      simp [RG]
      omega
    rw [e1, e2]
    exact CFSG.KC.AE6Tri.prep_pidn'

open Certificates.A6h2Swap in
theorem certificate399001 : Certificates.A6h2Swap.swapCheck () = true :=
  CFSG.KC.A6h2Swap.swapCheck_of prep_RG KernelA6h2.swapK_ok

end Certificates
