module

public import CFSG.Sporadic.J4.QT2LocNative
public meta import CFSG.Sporadic.J4.QT2LocNative
public import Certificates.Certificate4002

public section

namespace CFSG.Sporadic.J4.QT2

open CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT

theorem tClosed_true : chkTClosed = true :=
  Certificates.certificate4002.1

theorem chkD_true : chkD (locMats ()) (locInvs ()) = true :=
  Certificates.certificate4002.2.1

theorem one_mem_tMasks : (1 : Nat) ∈ tMasks :=
  Certificates.certificate4002.2.2

end CFSG.Sporadic.J4.QT2
