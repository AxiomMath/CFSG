module

public import CFSG.Sporadic.Co1Block.TwoCData
public import CFSG.Sporadic.Co1Block.Iota
public import CFSG.Sporadic.Co1Block.CentCheck
public meta import CFSG.Sporadic.Co1Block.TwoCData
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
public import CFSG.Sporadic.Co1Block.TwoCCheckInputs
public import Certificates.Certificate2047

public section

namespace CFSG.Sporadic.Co1Block

open CFSG.Sporadic.Co1Schreier.Native CFSG.Sporadic.SmallF2.Native CFSG.Sporadic.Co1.InvNative
  CFSG.Sporadic.Co1.TwoBNative

theorem twoC_cent_check : Native.centCheckOf iotaCRows twoCD1 twoCBray twoCD2 twoCVBase
    twoCVGens twoCVSizes = true :=
  Certificates.certificate2047.1

theorem twoC_q_check : Native.qCheckOf iotaCRows twoCD1 twoCBray twoCD2 twoCQRows 2048 twoCRoots
    twoCCGens twoCCSizes = true :=
  Certificates.certificate2047.2.1

theorem twoC_misc_check : twoCMiscOf iotaCRows twoCQRows = true :=
  Certificates.certificate2047.2.2

end CFSG.Sporadic.Co1Block
