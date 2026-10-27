module

public import CFSG.Sporadic.J4.QT2LocCntNative
public meta import CFSG.Sporadic.J4.QT2LocCntNative
public import Certificates.Certificate4003

public section

namespace CFSG.Sporadic.J4.QT2

open CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT

theorem chkZMasks_true : chkZMasks = true :=
  Certificates.certificate4003.1

theorem chkCntZ_true : chkCntZ (locMats ()) (locInvs ()) = true :=
  Certificates.certificate4003.2.1

theorem orb6_ok : vorbOK locTabs rep6Vec orb6 28336 = true :=
  Certificates.certificate4003.2.2.1

theorem pathInv_ok : (List.range 7).all (fun ℓ =>
    eqRows (mulRows (pathRows (repPaths.getD ℓ [])) (invRows (pathRows (repPaths.getD ℓ []))))
      idRows) = true :=
  Certificates.certificate4003.2.2.2

end CFSG.Sporadic.J4.QT2
