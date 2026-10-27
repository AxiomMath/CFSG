
module

public import CFSG.Sporadic.Co1Block.IotaCheckBase

public import CFSG.Sporadic.Co1Block.IotaData
public import CFSG.Sporadic.Schreier.Co1StabCheck
public import CFSG.Sporadic.Co2Schreier.ThirdCheck
public meta import CFSG.Sporadic.Co1Block.IotaData
public meta import CFSG.Sporadic.Schreier.Co1StabCheck
public meta import CFSG.Sporadic.Schreier.Co1ThreeLocal
public meta import CFSG.Sporadic.Schreier.Co1StabData
public meta import CFSG.Sporadic.Co2Schreier.ThirdCheck
public meta import CFSG.Sporadic.Co2Schreier.Arrays
public meta import CFSG.Sporadic.Co2Schreier.TextCheck
public meta import CFSG.Sporadic.Co2Cert.Cert
public meta import Certificates.Data.CFSGNative.Co1Schreier.Base
public meta import Certificates.Data.CFSGNative.Co1.Data
public meta import Certificates.Data.CFSGNative.HS.SmallF2
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Chain
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Data
public import CFSG.Sporadic.Co1Block.IotaCheckInputs
public import Certificates.Certificate2042

public section

namespace CFSG.Sporadic.Co1Block

open CFSG.Monster.B.Co2.Native CFSG.Sporadic.Co2Schreier

theorem iota_check : iotaCheckOf CFSG.Sporadic.Co1Schreier.Native.hRows0
    CFSG.Sporadic.Co1Schreier.Native.hRows1 aArrs zArr uArr qArrs = true :=
  Certificates.certificate2042

end CFSG.Sporadic.Co1Block
