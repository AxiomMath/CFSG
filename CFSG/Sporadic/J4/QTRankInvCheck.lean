module

public import CFSG.Sporadic.J4.QTRankInvNative
public meta import CFSG.Sporadic.J4.QTRankInvNative
public import Certificates.Certificate4025

public section

namespace CFSG.Sporadic.J4.QT

theorem invAllOK_true : invAllOK = true :=
  Certificates.certificate4025.1

theorem invData_cover :
    ∀ e < 1024, isInvE e = true → ∃ x ∈ invData, x.1 = e :=
  Certificates.certificate4025.2.1

theorem orbit_roots : ∀ o ∈ orbits, o.1 = 1 ∨ o.1 = 3 :=
  Certificates.certificate4025.2.2

end CFSG.Sporadic.J4.QT
