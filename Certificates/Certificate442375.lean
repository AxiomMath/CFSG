module

public import CFSG.GH74.KGroups.L33Inputs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FHChk
import CFSG.Certificates.Kernel.PermCent.SmallF3TwinSound
import Certificates.Kernel.PermCent.K442375

public section

open CFSG.GH74.KGroups CFSG.Certificates.Kernel.PkCV CFSG.Certificates.Kernel.PkCV.SmallF3T

namespace Certificates

open CFSG.GH74.KGroups in
open CFSG.OddStandard.SmallF3.Omega (fhO3Chk) in
theorem certificate442375 : fhO3Chk (elemsT L33.QA) (elemsT L33.QP) = true := by
  rw [elemsT_eq_elemsC, elemsT_eq_elemsC, fhO3Chk_C]
  exact K442375.k442375

end Certificates
