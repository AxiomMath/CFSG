module

public import CFSG.Sporadic.J4.QT2LocZNative
public meta import CFSG.Sporadic.J4.QT2LocZNative
public import Certificates.Certificate4016
public meta import CFSG.Sporadic.J4.QT2LocNative
public import CFSG.Sporadic.J4.QT2LocNative

public section

namespace CFSG.Sporadic.J4.QT2

open CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT

theorem gWord_check :
    chkCommRoot (locMats ()) (locInvs ()) gWord = true :=
  Certificates.certificate4016.1

theorem y7Word_check :
    chkOrder (locMats ()) (locInvs ()) y7Word 7 = true :=
  Certificates.certificate4016.2.1

theorem y11Word_check :
    chkOrder (locMats ()) (locInvs ()) y11Word 11 = true :=
  Certificates.certificate4016.2.2

end CFSG.Sporadic.J4.QT2
