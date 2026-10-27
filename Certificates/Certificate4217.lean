module

public import Certificates.Data.A6B1
public import CFSG.GH74.KGroups.A6Inputs
import CFSG.Certificates.Kernel.Census.CatFacts.PkEnum
import Certificates.Kernel.KGroupsE.K4217

public section

namespace Certificates

open CFSG.GH74.KGroups CFSG.Certificates.Kernel.PkEnum CertificateChecks.KernelKGroupsE

open CFSG.GH74.KGroups CFSG.Quasithin.E217A6 in
theorem certificate4217 : a6Check (elemsT A6.QP) (elemsT A6.QA) = true :=
  by simp only [elemsT_eq_elemsV]; exact a6_4217K

end Certificates
