module

public import CFSG.Sporadic.Schreier.TitsStabCheck
public import CFSG.Certificates.NativeInvariantMerge
public import CFSG.Sporadic.Schreier.TitsLocal
public meta import CFSG.Sporadic.Schreier.TitsLocal
public meta import CFSG.Sporadic.Schreier.TitsData
public meta import CFSG.Sporadic.Schreier.TitsArrays
public meta import CFSG.Sporadic.Schreier.TitsBasic
public meta import CFSG.Sporadic.Schreier.TitsCertCheck
public meta import CFSG.Sporadic.Schreier.TitsLocalCheck
public meta import CFSG.Sporadic.Schreier.TitsActionCheck
public meta import CFSG.Sporadic.Schreier.TitsOrbit
public meta import CFSG.Sporadic.Schreier.TitsStabCheck
public meta import CFSG.Certificates.NativeInvariantMerge
public meta import Certificates.Data.CFSGNative.Schreier.Check
public meta import Certificates.Data.CFSGNative.Schreier.Merge
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Chain
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Data

public section

namespace CFSG.Sporadic.Schreier.Tits

open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2.Native

@[expose] def titsH0Idx : List ℕ := (List.range 13).filter fun j => (titsDerivedArrs[j]!)[0]! == 0

@[expose] def titsH0Arrs : Array (Array ℕ) := (titsH0Idx.map fun j => titsDerivedArrs[j]!).toArray

@[expose] def titsH0Forest : Array ℕ × Array ℕ × Array ℕ × Array ℕ :=
  orbitForest 1755 titsH0Arrs #[0, 1, 6, 24, 87]

@[expose] def titsNStarArrs : Array (Array ℕ) :=
  (titsNWords.map fun w => wordArr 2925 titsTStarArrs w).toArray

@[expose] def titsNForest : Array ℕ × Array ℕ × Array ℕ × Array ℕ :=
  orbitForest 2925 titsNStarArrs #[0, 1, 7, 27, 107, 141]

@[expose] def titsOrigMerge (l : ℕ) : List (Fin 2 × Fin 1755 × Fin 1755) :=
  (titsOrigMergeVals l).map fun m => (finPt 2 m.1, finPt 1755 m.2.1, finPt 1755 m.2.2)

end CFSG.Sporadic.Schreier.Tits
