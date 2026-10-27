module

public import CFSG.Sporadic.SuzOddCore.ArraysCheck
public import Certificates.Data.CFSGNative.MonsterB.Co2Chain
public import Certificates.Data.CFSGNative.Perm.Chain
public meta import CFSG.Sporadic.SuzOddCore.ArraysCheck
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Chain
public meta import Certificates.Data.CFSGNative.Perm.Chain

public section

namespace CFSG.Sporadic.SuzOddCore

open CFSG.Monster.B.Co2.Native CFSG.Sporadic.Th.Native CFSG.Perm.Native

@[expose] def certStrongInvs : Array (Array Nat) := certStrongArrs.map (invCand 22880)

@[expose] def certLetters : Array Table :=
  Array.ofFn (n := 20) fun l =>
    if l.val % 2 = 0 then (certStrongArrs[l.val / 2]!).map UInt32.ofNat
    else (certStrongInvs[l.val / 2]!).map UInt32.ofNat

@[expose] def certLevelIdx (i : Nat) : List Nat :=
  [[0, 1, 2, 3, 4, 5, 6, 7, 8, 9], [2, 3, 4, 5, 6, 7, 8, 9], [4, 5, 6, 7, 8, 9], [9], [], [],
    []].getD i []

@[expose] def certLevelLetters (i : Nat) : Array Nat :=
  ((certLevelIdx i).flatMap fun j => [2 * j, 2 * j + 1]).toArray

@[expose] def certTree (i : Nat) : Tree :=
  treeBFS 22880 (certBaseNat.getD i 0) certLetters (certLevelLetters i)

@[expose] def certOrbitSizes : List Nat := [22880, 8505, 1152, 2, 1, 1]

end CFSG.Sporadic.SuzOddCore
