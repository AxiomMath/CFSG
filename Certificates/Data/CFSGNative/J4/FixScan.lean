module

public import Certificates.Data.CFSGNative.J4.Store

public section

namespace CFSG.Sporadic.J4.Native

@[inline, expose] def fixScanAt (keys : ByteArray) (T : Array V2) (pts : List V2) (i : Nat) :
    Bool :=
  let v := rdV2 keys i
  !((frApply T v).beq v) || pts.any fun w => w.beq v

@[expose] def fixScanOK (keys : ByteArray) (n : Nat) (T : Array V2) (pts : List V2)
    (chunks : Nat) : Bool :=
  parAllS n chunks (fixScanAt keys T pts)

end CFSG.Sporadic.J4.Native
