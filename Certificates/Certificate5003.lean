module

public import CFSG.GH74.E2.Q8C2Check
import CFSG.Certificates.Kernel.PermCent.KGrpC3Sound
import Certificates.Kernel.PermCent.K5003
public import CFSG.GH74.KGroups.A6Inputs
public import Certificates.Certificate43

public section

open CFSG.GH74.KGroups CFSG.Certificates.Kernel.PkCV CFSG.Certificates.Kernel.PkCV.KGrp

namespace Certificates

open CFSG in
open CFSG.GH74 in
open CFSG.GH74.E2 in
open CFSG.GH74.KGroups in
theorem certificate5003 : q8c2free (elemsT A6.QA) = true := by
  rw [elemsT_eq_elemsC, q8c2free_C]
  exact K5003.k5003

end Certificates
