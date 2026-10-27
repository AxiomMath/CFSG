
module

public import CFSG.Sporadic.Co2Schreier.ThirdCheckBase

public import CFSG.Sporadic.Co2Schreier.WitCheck
public import CFSG.Sporadic.Co2Schreier.CoreCheck
public import CFSG.Sporadic.Co2Cert.FaithfulCheck
public import CFSG.Sporadic.Co2Schreier.SylowCheck
public meta import CFSG.Sporadic.Co2Schreier.WitCheck
public meta import CFSG.Sporadic.Co2Schreier.SylowCheck
public meta import CFSG.Sporadic.Co2Schreier.CoreCheck
public meta import CFSG.Sporadic.Co2Cert.FaithfulCheck
public import CFSG.Sporadic.Co2Schreier.ThirdCheckInputs
public import Certificates.Certificate2061

public section

namespace CFSG.Sporadic.Co2Schreier

open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.Monster.B.Mathieu
  CFSG.Sporadic.Co2Cert CFSG.Sporadic.SmallF2.Native

theorem third_check : thirdCheck (thirdLevels witRec) witRec.third.baseIndices.toArray uArr
    (rawLevels 2300 co2StrongArrs co2BaseArr) co2BaseArr = true :=
  Certificates.certificate2061.1

theorem e_check : eCheck co2PosTable witRec (rawLevels 2300 co2StrongArrs co2BaseArr) co2BaseArr
    uArr = true :=
  Certificates.certificate2061.2

end CFSG.Sporadic.Co2Schreier
