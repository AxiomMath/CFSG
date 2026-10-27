module

public import Certificates.Data.L27B1
public import CFSG.GH74.KGroups.L27Inputs
import CFSG.Certificates.Kernel.Census.CatFacts.PkEnum
import Certificates.Kernel.KGroupsE.K4218

public section

open CFSG.GH74.KGroups CFSG.Quasithin.E217B1L27 CFSG.Certificates.Kernel.PkEnum

namespace Certificates

open CertificateChecks

open CFSG.GH74.KGroups CFSG.Quasithin.E217B1L27 in
theorem certificate4218 : l27Check (elemsT L27.QP) = true := by
  rw [elemsT_eq_elemsV]
  exact KernelKGroupsE.l27_4218K

end Certificates
