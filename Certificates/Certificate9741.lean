module

public import CFSG.ClassicalInvolution.Q3.ONanTA3SmallCheck
public import CFSG.GH74.KGroups.L33Inputs
import CFSG.Certificates.Kernel.PermCent.KGrpC3Sound
import CFSG.Certificates.Kernel.PermCent.GoodCSound
import Certificates.Kernel.PermCent.K9741G

public section

open CFSG.GH74.KGroups CFSG.Certificates.Kernel.PkCV CFSG.Certificates.Kernel.PkCV.KGrp
  CFSG.Certificates.Kernel.PkCV.Good

namespace Certificates

theorem certificate9741 : CFSG.ClassicalInvolution.Q3.TA3.Check.goodCheck 100
    (CFSG.GH74.KGroups.elemsT CFSG.GH74.KGroups.L33.QP) = true := by
  rw [elemsT_eq_elemsC, goodCheck_ev, goodCheck_C]
  exact K9741G.k9741

end Certificates
