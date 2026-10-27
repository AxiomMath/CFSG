module

public import CFSG.Sporadic.SuzOddCore.InvTCheck
public import Certificates.Data.CFSGNative.PSL3Four.Basic
public meta import CFSG.Sporadic.SuzOddCore.InvTCheck
public meta import Certificates.Data.CFSGNative.PSL3Four.Basic
public import CFSG.Sporadic.SuzOddCore.SylowCheckInputs
public import Certificates.Certificate2307

public section

namespace CFSG.Sporadic.SuzOddCore

open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.PSL3Four.Native

theorem sylowAll_check : sylowChecks sylowEnum fusionEnums = true :=
  Certificates.certificate2307

end CFSG.Sporadic.SuzOddCore
