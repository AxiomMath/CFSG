module

public import CFSG.Sporadic.Schreier.TitsCertCheck
public meta import CFSG.Sporadic.Schreier.TitsData
public meta import CFSG.Sporadic.Schreier.TitsArrays
public meta import CFSG.Sporadic.Schreier.TitsBasic
public meta import Certificates.Data.CFSGNative.Schreier.Check
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Chain
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Data
public meta import CFSG.Sporadic.Schreier.TitsCertCheck

public section

namespace CFSG.Sporadic.Schreier.Tits

open CFSG.Certificates.Native CFSG.Monster.B.Co2.Native

@[expose] def titsLineBuckets : Array (List ℕ) :=
  (List.range 8775).foldl (fun acc j => acc.modify titsKappaArr[j]! fun l => l ++ [j])
    (Array.replicate 2925 [])

@[expose] def titsLineFlagArr : Array ℕ :=
  (titsLineBuckets.toList.map fun l =>
    l.mergeSort fun a b => decide (titsBetaArr[a]! ≤ titsBetaArr[b]!)).flatten.toArray

@[expose] def titsLinePtArr : Array ℕ := titsLineFlagArr.map fun j => titsBetaArr[j]!

@[expose] def titsLinePos (v x : ℕ) : ℕ :=
  if titsLinePtArr[3 * v]! = x then 0 else if titsLinePtArr[3 * v + 1]! = x then 1
  else if titsLinePtArr[3 * v + 2]! = x then 2 else 3

@[expose] def titsLineKey (v : ℕ) : ℕ :=
  (titsLinePtArr[3 * v]! * 1755 + titsLinePtArr[3 * v + 1]!) * 1755 + titsLinePtArr[3 * v + 2]!

end CFSG.Sporadic.Schreier.Tits
