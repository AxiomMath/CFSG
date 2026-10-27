module

public import CFSG.Sporadic.Co1Block.TwoAData
public import CFSG.Sporadic.Co1Block.Iota
public import CFSG.Sporadic.Co1Block.CentCheck
public meta import CFSG.Sporadic.Co1Block.TwoAData
public meta import CFSG.Sporadic.Co1Block.IotaData
public meta import CFSG.Sporadic.Co1Block.Iota
public meta import CFSG.Sporadic.Co1Block.CentCheck
public meta import CFSG.Sporadic.Schreier.Co1ChainCheck
public meta import CFSG.Sporadic.Schreier.Co1StabCheck
public meta import CFSG.Sporadic.Schreier.Co1ThreeLocal
public meta import CFSG.Sporadic.Schreier.Co1StabData
public meta import Certificates.Data.CFSGNative.Co1Schreier.Base
public meta import Certificates.Data.CFSGNative.Co1.Data
public meta import Certificates.Data.CFSGNative.Co1.Involutions
public meta import Certificates.Data.CFSGNative.Co1.TwoB
public meta import Certificates.Data.CFSGNative.HS.SmallF2
public import CFSG.Sporadic.Co1Block.TwoACheckInputs
public import Certificates.Certificate2044

public section

namespace CFSG.Sporadic.Co1Block

open CFSG.Sporadic.Co1Schreier.Native CFSG.Sporadic.SmallF2.Native CFSG.Sporadic.Co1.InvNative
  CFSG.Sporadic.Co1.TwoBNative

theorem twoA_cent_check : Native.centCheckOf iotaARows twoAD1 twoABray twoAD2 twoAVBase
    twoAVGens twoAVSizes = true :=
  Certificates.certificate2044.1

theorem twoA_q_check : Native.qCheckOf iotaARows twoAD1 twoABray twoAD2 twoAQRows 512 twoARoots
    twoACGens twoACSizes = true :=
  Certificates.certificate2044.2.1

theorem twoA_misc_check : twoAMiscOf iotaARows twoAQRows = true :=
  Certificates.certificate2044.2.2

end CFSG.Sporadic.Co1Block
