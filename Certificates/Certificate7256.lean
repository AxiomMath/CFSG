module

public import Certificates.Kernel.J4M4Card.Glue
public import Certificates.Kernel.J4M4Card.PsiGlue

public section

namespace Certificates

open CertificateChecks

open CFSG.Quasithin.J4M4Card in
theorem certificate7256 : (chkT () = true) ∧ (chkMasks () = true) ∧ (CFSG.Quasithin.J4M4Card.chkWit () = true) ∧
    (chkDistinct () = true) ∧ (chkPsi () = true) ∧ (chkKE () = true) :=
  ⟨KernelJ4M4Card.t_ok, KernelJ4M4Card.chkMasks_ok, KernelJ4M4Card.chkWit_ok,
    KernelJ4M4Card.dist_ok, KernelJ4M4Card.chkPsi_ok, KernelJ4M4Card.chkKE_ok⟩

end Certificates
