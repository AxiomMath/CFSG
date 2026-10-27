
module

public import CFSG.Sporadic.Schreier.Co1OrbEnumCheck
public import CFSG.Sporadic.Schreier.Co1StabData
public import CFSG.Sporadic.Schreier.Co1FullOrbCheckBase
public import CFSG.Sporadic.Schreier.Co1ThreeLocal
public meta import CFSG.Sporadic.Schreier.Co1OrbEnumCheck
public meta import CFSG.Sporadic.Schreier.Co1StabData
public meta import CFSG.Sporadic.Schreier.Co1FullOrbCheckBase
public meta import CFSG.Sporadic.Schreier.Co1ThreeLocal
public meta import Certificates.Data.CFSGNative.Co1Schreier.Base
public meta import Certificates.Data.CFSGNative.Co1.Data
public meta import Certificates.Data.CFSGNative.HS.SmallF2
public meta import Certificates.Data.CFSGNative.Th.Tables
public meta import Certificates.Data.CFSGNative.Th.Orbit

public section

namespace CFSG.Sporadic.Co1Schreier

namespace Native

open CFSG.Sporadic.SmallF2.Native CFSG.Sporadic.Th.Native

@[expose] def hRows0 : Rows := word [aR, bR] [inv aR, inv bR] (Data.stabWord0.map Int.ofNat)

@[expose] def hRows1 : Rows := word [aR, bR] [inv aR, inv bR] (Data.stabWord1.map Int.ofNat)

@[expose] def stabVec (k : Nat) : Nat := Data.stabVecs.getD k 0

@[expose] def stabSize (k : Nat) : Nat := [1, 46575, 47104, 4600].getD k 0

@[expose] def stabOrb (k : Nat) : VOrbit :=
  vOrbitBFS 24 (transposeRows 24 hRows0) (transposeRows 24 hRows1) (stabVec k) (stabSize k)

@[expose] def stabOrbCheck : Bool :=
  mul hRows0 (inv hRows0) == one && mul hRows1 (inv hRows1) == one && wf hRows0 && wf hRows1 &&
    (List.range 4).all fun k =>
      enumOK (transposeRows 24 hRows0) (transposeRows 24 hRows1) (stabVec k) (stabSize k)
        (stabOrb k)

@[expose] def stabXCheckOf (O : VOrbit) : Bool :=
  (List.range 4).all fun k => (List.range 98280).any fun i => O.pts[i]! == stabVec k

@[expose] def stabXCheck : Bool := stabXCheckOf (fullOrb 2)

@[expose] def witRows (m : Nat) : List Rows :=
  (Data.fixWords.getD m []).map fun w => word [hRows0, hRows1] [inv hRows0, inv hRows1] w

@[expose] def witCheck : Bool :=
  (List.range 3).all fun m => (witRows m).all fun s =>
    act s (stabVec 0) == stabVec 0 && act s (stabVec (m + 1)) == stabVec (m + 1) && wf s

@[expose] def fixCoef (ws : List Rows) (c u : Nat) : Bool :=
  ((ws.getD (c / 24) one).getD (c % 24) 0 ^^^ (1 <<< (c % 24))).testBit u

@[expose] def fixComb (ws : List Rows) (cs : List Nat) (v : Nat) : Bool :=
  cs.foldl (fun b c => b ^^ fixCoef ws c v) false

@[expose] def fixFreeOf (m : Nat) : Nat × Nat := Data.fixFree.getD m (0, 0)

@[expose] def fixStepsOf (m u : Nat) : List Nat := (Data.fixSteps.getD m []).getD u []

@[expose] def nonFree (m u : Nat) : Bool := u != (fixFreeOf m).1 && u != (fixFreeOf m).2

@[expose] def fixCheckOf (m : Nat) (ws : List Rows) : Bool :=
  decide ((fixFreeOf m).1 < 24) && decide ((fixFreeOf m).2 < 24) &&
    ((stabVec 0).testBit (fixFreeOf m).1 && (stabVec (m + 1)).testBit (fixFreeOf m).2) !=
      ((stabVec 0).testBit (fixFreeOf m).2 && (stabVec (m + 1)).testBit (fixFreeOf m).1) &&
    (List.range 24).all fun u => !nonFree m u ||
      (fixComb ws (fixStepsOf m u) u &&
        (List.range 24).all (fun v => v == u || !nonFree m v || !fixComb ws (fixStepsOf m u) v) &&
        (fixStepsOf m u).all fun c => decide (c / 24 < ws.length))

@[expose] def fixCheck : Bool := (List.range 3).all fun m => fixCheckOf m (witRows m)

@[expose] def inEnum (O : VOrbit) (n v : Nat) : Bool := (List.range n).any fun i => O.pts[i]! == v

@[expose] def memCheckOf (m : Nat) (O : VOrbit) : Bool :=
  !inEnum O (stabSize (m + 1)) 0 && !inEnum O (stabSize (m + 1)) (stabVec 0) &&
    inEnum O (stabSize (m + 1)) (stabVec 0 ^^^ stabVec (m + 1)) == (m == 2)

@[expose] def memCheck : Bool := (List.range 3).all fun m => memCheckOf m (stabOrb (m + 1))

end Native

end CFSG.Sporadic.Co1Schreier
