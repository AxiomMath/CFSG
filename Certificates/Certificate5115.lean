module

public import CFSG.GH74.KGroups.Sz8TablesInputs
import CFSG.Certificates.Kernel.PermCent.KGrpC2Sound
import Certificates.Kernel.PermCent.K5115

public section

open CFSG.GH74.KGroups CFSG.GH74.KGroups.Sz8 CFSG.Certificates.Kernel.PkCV
  CFSG.Certificates.Kernel.PkCV.KGrp

namespace Certificates

open CFSG in
open CFSG.GH74 in
open CFSG.GH74.KGroups in
open CFSG.Certificates CFSG.Sporadic.Schreier CFSG.Blueprint CFSG.Quasithin CFSG.GH74.KGroups.Sz8 in
theorem certificate5115 : NativeChecks.centInCheck (elemsT CFSG.GH74.KGroups.Sz8.QA) (elemsT QS) = true := by
  rw [elemsT_eq_elemsC, elemsT_eq_elemsC, centIn_C]
  exact K5115.k5115

end Certificates
