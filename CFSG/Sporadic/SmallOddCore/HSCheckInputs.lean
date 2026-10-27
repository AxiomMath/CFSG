module

public import CFSG.Sporadic.SmallOddCore.HSData
public import CFSG.Sporadic.Schreier.PairHSCheck
public meta import CFSG.Sporadic.SmallOddCore.HSData
public meta import CFSG.Sporadic.Schreier.PairHSCheck

public section

namespace CFSG.Sporadic.SmallOddCore

open CFSG.Sporadic.Th.Native CFSG.Sporadic.SmallOddCore.Native CFSG.Sporadic.Schreier
open CFSG.Sporadic.Schreier.Native
open CFSG.Monster.B.Co2.Native

@[expose] def hsPGTbls : Array Table :=
  #[hsStrongArrs[0]!.map UInt32.ofNat, hsStrongArrs[1]!.map UInt32.ofNat]

@[expose] def hsPGInvTbls : Array Table := hsPGTbls.map (invT 3850)

@[expose] def hsSift (T : Table) : Bool :=
  siftA 3850 PairHS.levels PairHS.baseArr 0 (natArr T)

@[expose] def hsStabTbls : List Table :=
  ((List.range 8).map fun j => hsStrongArrs[j]!.map UInt32.ofNat).filter fun s => ap s 0 == 0

@[expose] def hsStabOK : Bool :=
  hsStabTbls.all (fun s => hsSift s && ap s 0 == 0) &&
    (List.range 3850).all fun x => x == 0 || hsStabTbls.any fun s => ap s x != x

end CFSG.Sporadic.SmallOddCore
