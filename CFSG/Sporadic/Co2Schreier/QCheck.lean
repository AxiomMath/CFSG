module

public import CFSG.Sporadic.Co2Schreier.WitCheck
public import CFSG.Sporadic.Co2Schreier.SylowCheck
public import Certificates.Data.CFSGNative.HS.SmallF2
public meta import CFSG.Sporadic.Co2Schreier.WitCheck
public meta import CFSG.Sporadic.Co2Schreier.SylowCheck
public meta import Certificates.Data.CFSGNative.HS.SmallF2
public import CFSG.Sporadic.Co2Schreier.QCheckInputs
public import Certificates.Certificate2056

public section

namespace CFSG.Sporadic.Co2Schreier

open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.Sporadic.SmallF2.Native

theorem qmod_check : qmodCheck witRec = true :=
  Certificates.certificate2056

end CFSG.Sporadic.Co2Schreier
