module

public import CFSG.GH74.KGroups.L33Inputs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L34GXC6Chk
import CFSG.Certificates.Kernel.Census.CatFacts.PkEnum
import Certificates.Kernel.KGroupsE.K442270

public section

namespace Certificates

open CFSG.GH74.KGroups CFSG.Certificates.Kernel.PkEnum CertificateChecks.KernelKGroupsE

open CFSG.GH74.KGroups in
open CFSG.OddStandard.SmallF3.Omega (c6free) in
theorem certificate442270 : c6free (elemsT L33.QA) (elemsT L33.QP) = true :=
  by simp only [elemsT_eq_elemsV]; exact c6_442270K

end Certificates
