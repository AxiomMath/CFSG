module

public import CFSG.Sporadic.Co2Schreier.ThirdCheck
public import CFSG.Sporadic.Co2InvData
public meta import CFSG.Sporadic.Co2Schreier.ThirdCheck
public meta import CFSG.Sporadic.Co2InvData
public import CFSG.Sporadic.Co2Schreier.ClassCheckInputs
public import Certificates.Certificate2050

public section

namespace CFSG.Sporadic.Co2Schreier

open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.Monster.B.Mathieu
  CFSG.Sporadic.Co2Cert CFSG.Sporadic.SmallF2.Native

theorem class_check : classCheck co2PosTable zArr tArr uArr = true :=
  Certificates.certificate2050

end CFSG.Sporadic.Co2Schreier
