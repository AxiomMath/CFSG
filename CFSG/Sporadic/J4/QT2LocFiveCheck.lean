module

public import CFSG.Sporadic.J4.QT2LocFiveNative
public meta import CFSG.Sporadic.J4.QT2LocFiveNative
public import Certificates.Certificate4004
public meta import CFSG.Sporadic.J4.QT2LocNative
public import CFSG.Sporadic.J4.QT2LocNative

public section

namespace CFSG.Sporadic.J4.QT2

open CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT

theorem chkFivePow_true : chkFivePow = true :=
  Certificates.certificate4004.1

theorem chkFiveMasks_true : chkFiveMasks = true :=
  Certificates.certificate4004.2

end CFSG.Sporadic.J4.QT2
