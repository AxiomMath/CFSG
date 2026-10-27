module

public import CFSG.Sporadic.J4.QTOutMatNative
public meta import CFSG.Sporadic.J4.QTOutMatNative
public import Certificates.Certificate4022
public meta import CFSG.Sporadic.J4.QTRankWitNative

public section

namespace CFSG.Sporadic.J4.QT

open CFSG.Sporadic.J4.Native

theorem x0_pow : eqRows (powRows (xRowsOf 1) 23) idRows = true :=
  Certificates.certificate4022.1

theorem x0_wf : wfRows (xRowsOf 1) = true :=
  Certificates.certificate4022.2.1

theorem x0_ne : eqRows (xRowsOf 1) idRows = false :=
  Certificates.certificate4022.2.2

end CFSG.Sporadic.J4.QT
