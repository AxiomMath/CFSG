module

public import CFSG.Sporadic.Schreier.TitsActionCheck
public import CFSG.Sporadic.Schreier.TitsLocalCheck
public import CFSG.Sporadic.Schreier.TitsOrbit
public meta import CFSG.Sporadic.Schreier.TitsData
public meta import CFSG.Sporadic.Schreier.TitsArrays
public meta import CFSG.Sporadic.Schreier.TitsBasic
public meta import Certificates.Data.CFSGNative.Schreier.Check
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Chain
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Data
public meta import CFSG.Sporadic.Schreier.TitsCertCheck
public meta import CFSG.Sporadic.Schreier.TitsLocalCheck
public meta import CFSG.Sporadic.Schreier.TitsActionCheck
public meta import CFSG.Sporadic.Schreier.TitsOrbit
public meta import Mathlib.GroupTheory.GroupAction.Transitive
public import Mathlib.GroupTheory.GroupAction.Transitive

public section

namespace CFSG.Sporadic.Schreier.Tits

open CFSG.Certificates.Native CFSG.Monster.B.Co2.Native

@[expose] def titsDFlagArrs : Array (Array ℕ) := Array.ofFn (n := 2) fun j =>
  commArr 8775 (wordArr 8775 titsFlagArrs (titsU j.val)) (wordArr 8775 titsFlagArrs (titsV j.val))

@[expose] def titsDStarArrs : Array (Array ℕ) := Array.ofFn (n := 2) fun j =>
  commArr 2925 (wordArr 2925 titsAStarArrs (titsU j.val))
    (wordArr 2925 titsAStarArrs (titsV j.val))

@[expose] def titsTFlagArrs : Array (Array ℕ) :=
  strongArrs 8775 titsDFlagArrs titsDerivedDerivations

@[expose] def titsTStarArrs : Array (Array ℕ) :=
  strongArrs 2925 titsDStarArrs titsDerivedDerivations

@[expose] def iterA (a : Array ℕ) : ℕ → ℕ → ℕ
  | 0, p => p
  | k + 1, p => a[iterA a k p]!

@[expose] def powFixes (a : Array ℕ) (k : ℕ) (pts : List ℕ) : Bool :=
  pts.all fun p => iterA a k p == p

end CFSG.Sporadic.Schreier.Tits
