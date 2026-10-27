module

public import CFSG.Sporadic.SuzOddCore.Arrays
public import Certificates.Data.CFSGNative.Suz.Certificate
public import Certificates.Data.CFSGNative.MonsterB.Co2Chain
public meta import CFSG.Sporadic.SuzOddCore.Arrays
public meta import Certificates.Data.CFSGNative.Suz.Certificate
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Chain
public import CFSG.Sporadic.SuzOddCore.RelabelCheckInputs
public import Certificates.Certificate2305

public section

namespace CFSG.Sporadic.SuzOddCore

open CFSG.Monster.B.Co2.Native CFSG.Sporadic.Th.Native

theorem relabel_check :
    relabelOK (CFSG.Sporadic.Suz.Native.orbitData ()).alpha
      (CFSG.Sporadic.Suz.Native.orbitData ()).beta = true :=
  Certificates.certificate2305

end CFSG.Sporadic.SuzOddCore
