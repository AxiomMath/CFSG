
module

public import CFSG.Sporadic.Co1Block.TwoAData
public import CFSG.Sporadic.Co1Block.IotaBase
public import CFSG.Sporadic.Co1Block.CentCheck
public meta import CFSG.Sporadic.Co1Block.TwoAData
public meta import CFSG.Sporadic.Co1Block.IotaData
public meta import CFSG.Sporadic.Co1Block.IotaBase
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

public section

namespace CFSG.Sporadic.Co1Block

open CFSG.Sporadic.Co1Schreier.Native CFSG.Sporadic.SmallF2.Native CFSG.Sporadic.Co1.InvNative
  CFSG.Sporadic.Co1.TwoBNative

@[expose] def twoAQRows : List Rows := (List.range 8).map iotaQRows

@[noinline, expose] def twoAMiscOf (Ra : Rows) (Qg : List Rows) : Bool :=
  (gtBFS Qg.toArray 512).pts.contains Ra && Qg.all (fun q => mul q Ra == mul Ra q) &&
    fixCount (transposeRows 24 Ra) == 65536 && (gtBFS Qg.toArray 512).pts.size == 512 &&
    mul Ra Ra == one && validRows Ra && Ra != one

end CFSG.Sporadic.Co1Block
