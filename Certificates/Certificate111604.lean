module

public import Certificates.Data.J2KJCoverC16
import Certificates.Kernel.J2Cover.C16K

public section

namespace Certificates

open CertificateChecks

theorem certificate111604 : CFSG.RankThree.PartTwo.J2Residue.C16.c16Check () = true :=
  KernelJ2Cover.C16K.c16_true

end Certificates
