
module

public import CFSG.Sporadic.FischerOddCore.Fi24R2KCheckBase

public import CFSG.Sporadic.FischerOddCore.Fi24R2Data
public import Certificates.Data.CFSGNative.Schreier.Check
public meta import CFSG.Sporadic.FischerOddCore.Fi24R2Data
public meta import Certificates.Data.CFSGNative.Schreier.Check
public import CFSG.Sporadic.FischerOddCore.Fi24R2KCheckInputs
public import Certificates.Certificate2077
public import Certificates.Certificate2077Base

public section

namespace CFSG.Sporadic.FischerOddCore

open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native

theorem fi24KChain_certificate : fi24KChainOK fi24KStrong fi24KWords = true :=
  Certificates.certificate2077.1

theorem fi24PChain_certificate : fi24PChainOK fi24PStrong fi24PWords = true :=
  Certificates.certificate2077.2.1

theorem fi24S_certificate : fi24SOK fi24KStrong fi24S0 fi24STree fi24PStrong = true :=
  Certificates.certificate2077.2.2

end CFSG.Sporadic.FischerOddCore
