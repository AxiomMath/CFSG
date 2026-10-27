module

public import Certificates.Kernel.SmithEK.ChkE

public section

namespace Certificates

open CertificateChecks

theorem certificate21265 :
    CFSG.SmithE.chkC8Pts = true ∧ CFSG.SmithE.chkC8Fix = true ∧
      CFSG.SmithE.chkC8Restr = true ∧ CFSG.SmithE.chkC8Irr = true ∧
      CFSG.SmithE.chkRigid = true :=
  ⟨KernelSmithEK.chkC8Pts_eq, KernelSmithEK.chkC8Fix_eq, KernelSmithEK.chkC8Restr_eq,
    KernelSmithEK.chkC8Irr_eq, KernelSmithEK.chkRigid_eq⟩

end Certificates
