module

public import Certificates.Data.L33E9
import CFSG.Certificates.Kernel.PermCent.E9CSound
import Certificates.Kernel.PermCent.K4211

public section

open CFSG.GH74.KGroups CFSG.Quasithin.E217L33 CFSG.Certificates.Kernel.PkCV
  CFSG.Certificates.Kernel.PkCV.E9

namespace Certificates

open CFSG.GH74.KGroups CFSG.Quasithin.E217L33 in
theorem certificate4211 : e9Check (elemsT L33.QP) L33.t0 ea eb = true := by
  rw [elemsT_eq_elemsC, eq_ev_cOf L33.t0, eq_ev_cOf ea, eq_ev_cOf eb, e9Check_C]
  exact K4211.k4211

end Certificates
