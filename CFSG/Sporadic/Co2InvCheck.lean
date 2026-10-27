module

public import CFSG.Sporadic.Co2InvData
public import CFSG.Sporadic.Co2Cert.FaithfulCheck
public import CFSG.Sporadic.Co2Cert.OrderCheck
public import Std.Data.HashMap
public meta import CFSG.Sporadic.Co2InvData
public meta import CFSG.Sporadic.Co2Cert.FaithfulCheck
public meta import CFSG.Sporadic.Co2Cert.OrderCheck
public meta import Std.Data.HashMap
public import CFSG.Sporadic.Co2InvCheckInputs
public import Certificates.Certificate3118

public section

namespace CFSG.Sporadic.Co2Inv

open CFSG.Sporadic.SmallF2.Native CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
  CFSG.Sporadic.Co2Cert

theorem gens_check :
    gensCheck (rawLevels 2300 co2StrongArrs co2BaseArr) co2PosTable = true :=
  Certificates.certificate3118.1

theorem cand_check : candCheck = true :=
  Certificates.certificate3118.2.1

theorem rank_check : rankCheck = true :=
  Certificates.certificate3118.2.2.1

theorem enum_check : enumCheck enumS candYs = true :=
  Certificates.certificate3118.2.2.2

end CFSG.Sporadic.Co2Inv
