module

public import CFSG.GH74.KGroups.U33Inputs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L34GXC6Chk
import CFSG.Certificates.Kernel.PermCent.SmallF3TwinSound
import Certificates.Kernel.PermCent.K442271

public section

open CFSG.GH74.KGroups CFSG.Certificates.Kernel.PkCV CFSG.Certificates.Kernel.PkCV.SmallF3T

namespace Certificates

open CFSG.GH74.KGroups in
open CFSG.OddStandard.SmallF3.Omega (c6free) in
theorem certificate442271 : c6free (elemsT U33.QA) (elemsT U33.QP) = true := by
  rw [elemsT_eq_elemsC, elemsT_eq_elemsC, c6free_C]
  exact K442271.k442271

end Certificates
