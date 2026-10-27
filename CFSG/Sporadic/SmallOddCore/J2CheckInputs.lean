module

public import CFSG.Sporadic.SmallOddCore.J2Data
public import CFSG.Sporadic.Schreier.PairJ2Check
public meta import CFSG.Sporadic.SmallOddCore.J2Data
public meta import CFSG.Sporadic.Schreier.PairJ2Check

public section

namespace CFSG.Sporadic.SmallOddCore

open CFSG.Sporadic.Th.Native CFSG.Sporadic.SmallOddCore.Native CFSG.Sporadic.Schreier
open CFSG.Sporadic.Schreier.PairNative CFSG.Monster.B.Co2.Native

@[expose] def j2PGTbls : Array Table :=
  #[j2StrongArrs[0]!.map UInt32.ofNat, j2StrongArrs[1]!.map UInt32.ofNat]

@[expose] def j2PGInvTbls : Array Table := j2PGTbls.map (invT 315)

@[expose] def j2Sift (T : Table) : Bool := siftA 315 PairJ2.levels PairJ2.baseArr 0 (natArr T)

@[expose] def j2StabTbls : List Table :=
  ((List.range 7).map fun j => j2StrongArrs[j]!.map UInt32.ofNat).filter fun s => ap s 1 == 1

@[expose] def j2StabOK : Bool :=
  j2StabTbls.all (fun s => j2Sift s && ap s 1 == 1) &&
    (List.range 315).all fun x => x == 1 || j2StabTbls.any fun s => ap s x != x

end CFSG.Sporadic.SmallOddCore
