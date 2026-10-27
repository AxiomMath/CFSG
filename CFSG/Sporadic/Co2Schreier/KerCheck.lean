
module

public import CFSG.Sporadic.Co2Schreier.KerCheckBase

public import CFSG.Sporadic.Co2Schreier.WitCheck
public import CFSG.Sporadic.Co2Schreier.CoreCheck
public meta import CFSG.Sporadic.Co2Schreier.WitCheck
public meta import CFSG.Sporadic.Co2Schreier.CoreCheck
public import CFSG.Sporadic.Co2Schreier.KerCheckInputs
public import Certificates.Certificate2053

public section

namespace CFSG.Sporadic.Co2Schreier

open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.Monster.B.Mathieu
  CFSG.Sporadic.Co2Cert

theorem ker_check : kerCheck kerData = true :=
  Certificates.certificate2053

end CFSG.Sporadic.Co2Schreier
