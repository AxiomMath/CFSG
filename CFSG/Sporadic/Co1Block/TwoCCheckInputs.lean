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

public section

namespace CFSG.Sporadic.Co1Block

open CFSG.Sporadic.Co1Schreier.Native CFSG.Sporadic.SmallF2.Native CFSG.Sporadic.Co1.InvNative
  CFSG.Sporadic.Co1.TwoBNative

@[expose] def twoCQRows : List Rows :=
  let D₂ := dag (Native.brayElts (Native.brayRows iotaCRows twoCD1) twoCBray) twoCD2
  twoCQGens.map fun j => D₂.1.getD j one

@[noinline, expose] def twoCMiscOf (Rc : Rows) (Qg : List Rows) : Bool :=
  (gtBFS Qg.toArray 2048).pts.size == 2048 && Qg.all (fun q => mul q Rc == mul Rc q) &&
    Qg.all (fun q => mul q q == one) && Qg.all (fun q => Qg.all fun q' => mul q q' == mul q' q) &&
    mul Rc Rc == one && validRows Rc && Rc != one

end CFSG.Sporadic.Co1Block
