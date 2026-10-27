module

public import CFSG.Sporadic.SmallOddCore.McLData
public import CFSG.Sporadic.Schreier.PairMcLCheck
public meta import CFSG.Sporadic.SmallOddCore.McLData
public meta import CFSG.Sporadic.Schreier.PairMcLCheck

public section

namespace CFSG.Sporadic.SmallOddCore

open CFSG.Sporadic.Th.Native CFSG.Sporadic.SmallOddCore.Native CFSG.Sporadic.Schreier
open CFSG.Monster.B.Co2.Native

@[expose] def mclPGTbls : Array Table :=
  #[mclStrongArrs[0]!.map UInt32.ofNat, mclStrongArrs[1]!.map UInt32.ofNat]

@[expose] def mclPGInvTbls : Array Table := mclPGTbls.map (invT 275)

@[expose] def mclSift (T : Table) : Bool :=
  siftA 275 PairMcL.levels PairMcL.baseArr 0 (natArr T)

@[expose] def mclStabTbls : List Table :=
  ((List.range 13).map fun j => mclStrongArrs[j]!.map UInt32.ofNat).filter fun s => ap s 0 == 0

@[expose] def mclStabOK : Bool :=
  mclStabTbls.all (fun s => mclSift s && ap s 0 == 0) &&
    (List.range 275).all fun x => x == 0 || mclStabTbls.any fun s => ap s x != x

end CFSG.Sporadic.SmallOddCore
