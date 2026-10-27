module

public import Certificates.Data.LieSylRootWt
import Certificates.Kernel.LieSylRootWt.Glue

public section

namespace Certificates

open CertificateChecks

theorem certificate617001 :
    (Certificates.Data.LieSylRootWt.rootWeightStabCheck .G2 11 6 = true)
    ∧ (Certificates.Data.LieSylRootWt.rootWeightStabCheck .D4 11 24 = true)
    ∧ (Certificates.Data.LieSylRootWt.rootWeightStabCheck .F4 11 24 = true) :=
  ⟨KernelLieSylRootWt.ch617001G2, KernelLieSylRootWt.d4_holds, KernelLieSylRootWt.f4_holds⟩

end Certificates

end
