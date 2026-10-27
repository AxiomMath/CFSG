module

public import CFSG.Sporadic.SmallOddCore.J3Data
public import CFSG.Sporadic.Schreier.PairJ3Check
public meta import CFSG.Sporadic.SmallOddCore.J3Data
public meta import CFSG.Sporadic.Schreier.PairJ3Check

public section

namespace CFSG.Sporadic.SmallOddCore

open CFSG.Sporadic.Th.Native CFSG.Sporadic.SmallOddCore.Native CFSG.Sporadic.Schreier
open CFSG.Monster.B.Co2.Native

@[expose] def j3PGTbls : Array Table :=
  #[j3StrongArrs[0]!.map UInt32.ofNat, j3StrongArrs[1]!.map UInt32.ofNat]

@[expose] def j3PGInvTbls : Array Table := j3PGTbls.map (invT 6156)

@[expose] def j3Sift (T : Table) : Bool := siftA 6156 PairJ3.levels PairJ3.baseArr 0 (natArr T)

@[expose] def j3StabTbls : List Table :=
  ((List.range 5).map fun j => j3StrongArrs[j]!.map UInt32.ofNat).filter fun s => ap s 0 == 0

@[expose] def j3StabOK : Bool :=
  j3StabTbls.all (fun s => j3Sift s && ap s 0 == 0) &&
    (List.range 6156).all fun x => x == 0 || j3StabTbls.any fun s => ap s x != x

end CFSG.Sporadic.SmallOddCore
