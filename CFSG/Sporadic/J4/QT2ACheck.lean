module

public import CFSG.Sporadic.J4.QT2ANative
public meta import CFSG.Sporadic.J4.QT2ANative
public import Certificates.Certificate4000

public section

namespace CFSG.Sporadic.J4.QT2A

theorem chkMod_true : chkMod = true :=
  Certificates.certificate4000.1

theorem chkY_true : chkY = true :=
  Certificates.certificate4000.2.1

theorem chkYr5_true : chkYr (y5R ()) 5 = true :=
  Certificates.certificate4000.2.2.1

theorem chkYr7_true : chkYr (y7R ()) 7 = true :=
  Certificates.certificate4000.2.2.2.1

theorem chkYr11_true : chkYr (y11R ()) 11 = true :=
  Certificates.certificate4000.2.2.2.2.1

theorem chkQgens_true : chkQgens = true :=
  Certificates.certificate4000.2.2.2.2.2.1

theorem chkNotQzY_true : chkNotQzY = true :=
  Certificates.certificate4000.2.2.2.2.2.2.1

theorem chkNotQz5_true : chkNotQzPow (y5R ()) 5 = true :=
  Certificates.certificate4000.2.2.2.2.2.2.2.1

theorem chkNotQz7_true : chkNotQzPow (y7R ()) 7 = true :=
  Certificates.certificate4000.2.2.2.2.2.2.2.2.1

theorem chkNotQz11_true : chkNotQzPow (y11R ()) 11 = true :=
  Certificates.certificate4000.2.2.2.2.2.2.2.2.2.1

theorem chkWit_true : chkWit = true :=
  Certificates.certificate4000.2.2.2.2.2.2.2.2.2.2.1

theorem chkE_true : chkE = true :=
  Certificates.certificate4000.2.2.2.2.2.2.2.2.2.2.2.1

theorem chkQconj_true : chkQconj = true :=
  Certificates.certificate4000.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem chkLoc_true : chkLoc = true :=
  Certificates.certificate4000.2.2.2.2.2.2.2.2.2.2.2.2.2

end CFSG.Sporadic.J4.QT2A
