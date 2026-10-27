module

public import CFSG.Sporadic.FischerOddCore.Fi22ExtCheck
public import CFSG.Monster.B.Fischer.Fi22OuterCheck
public meta import CFSG.Sporadic.FischerOddCore.Fi22ExtCheck
public meta import CFSG.Monster.B.Fischer.Fi22OuterCheck
public import Certificates.Certificate2073

public section

namespace CFSG.Sporadic.FischerOddCore

open CFSG.Monster.B.Co2.Native CFSG.Monster.B.Fischer

theorem fi22Unitary_check : eqA 3510 (fi22ExtArr 23) (fi22OuterStrong3510 1)[0]! = true :=
  Certificates.certificate2073

end CFSG.Sporadic.FischerOddCore
