module

public import CFSG.Sporadic.SuzOddCore.CTICheckInputs

public section

namespace CFSG.Sporadic.SuzOddCore

open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.PSL3Four.Native

@[expose] def pushStrong (n : Nat) (S : Array (Array Nat)) : List (List Int) → Array (Array Nat)
  | [] => S
  | w :: ws => pushStrong n (S.push (wordA n S (rawInvs n S) w)) ws

@[expose] def k1Words : List (List Int) :=
  [[-6, -2, 4, 2], [5, 2], [-6, -4, 6, 2], [11, -6, 12, -10, 9, 2],
    [-11, 14, -6, -12, -5, 10, 2], [-15, 14, -11, 14, 12, -3, -2, 9, 3], [-11, -11, -2, 16, 2],
    [-15, -14, -13, 14, -12, -16, -2, 8, 4, 3]]

@[expose] def k1Strong : Array (Array Nat) := pushStrong 54 (kGens 1) k1Words

@[expose] def k1Base : Array Nat := #[0, 1, 2, 3, 4, 6]

@[expose] def qTabs : Array Tab := (enumOf 54 qGens 64).tabs

@[expose] def actGens : Array (Array Nat) :=
  Array.ofFn (n := 10) fun k => Array.ofFn (n := 64) fun p =>
    qTabs.toList.idxOf (conjTab 54 (kGens 1)[k.val]! (kInvs 1)[k.val]! qTabs[p.val]!)

@[expose] def actWords : List (List Int) :=
  [[-3, 6], [-5, 9], [-11, 12, 12, -2, 10], [-11, 13, -2, 10], [-13, -7, 13, 10, 10, 2],
    [-15, -13, -14, -7, -13, -3, -2, 5, 3]]

@[expose] def actStrong : Array (Array Nat) := pushStrong 64 actGens actWords

@[expose] def actBase : Array Nat := #[2, 1, 3, 4, 5]

end CFSG.Sporadic.SuzOddCore
