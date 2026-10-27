module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.ThCheck
import Certificates.Kernel.Th.Fam.C129003
import Certificates.Kernel.Th.Fam.Ctx

public section

namespace Certificates

open CertificateChecks

open CFSG.KC.Th.Expr

open CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic in
theorem certificate129003 : thDihCheck () = true := by
  have h := KernelTh.Fam.ok129003
  rw [← eqRows_eq_beq KernelTh.Fam.thCtx, ← eqRows_eq_beq KernelTh.Fam.thCtx] at h
  kernel_exact h

end Certificates
