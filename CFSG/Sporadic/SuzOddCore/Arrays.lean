module

public import CFSG.Sporadic.SuzOddCore.Text
public import Certificates.Data.CFSGNative.MonsterB.Co2Data

public section

namespace CFSG.Sporadic.SuzOddCore

open CFSG.Monster.B.Co2.Native

@[expose] def mtxTokens (s : String) : List String :=
  (s.splitToList Char.isWhitespace).filter (· ≠ "")

@[expose] def tokenVal (t : String) : Nat := t.toNat?.getD 0

@[expose] def mtxHeader (s : String) : List Nat := ((mtxTokens s).take 4).map tokenVal

@[expose] def mtxImages (s : String) : List Nat := ((mtxTokens s).drop 4).map tokenVal

@[expose] def mtxArr (s : String) : Array Nat := ((mtxImages s).map fun x => x - 1).toArray

def certArr (k : Nat) : Array Nat := hexTable 4 22880 (22880 * k) certChainText

@[expose] def certGenArrs : Array (Array Nat) := #[certArr 0, certArr 1]

@[expose] def certStrongArrs : Array (Array Nat) :=
  #[certArr 2, certArr 3, certArr 4, certArr 5, certArr 6, certArr 7, certArr 8, certArr 9,
    certArr 10, certArr 11]

@[expose] def certBaseNat : List Nat := [0, 1, 2, 3, 4, 5]

@[expose] def certDerivs : Array (List Int) :=
  #[[], [], [-2, 1, 2], [-1, -2, -3, -1, -2, -3, -1, -2, -1, -3, 1, -2, 1, 3, 1, 3, 1, 3, 2, 1],
    [-3, -4, 3, 4], [-1, -3, -4, -2, 1, 2, 4, 1], [-3, -6, -3, -6, 3, -5, -6, 3],
    [4, -5, -4, 3, -7, 4, 3], [-4, -7, 8, 3, -6, 4, 3], [9, 5, 9, -3, -7, -9, -6, 3, 4, 8, 3]]

@[expose] def certStabIdx : List Nat := [2, 3, 4, 5, 6, 7, 8, 9]

@[expose] def certStabOrbitSizes : List Nat := [1, 8505, 13608, 280, 486]

def certStabOrbit (t : Nat) : List Nat :=
  (hexTable 4 (certStabOrbitSizes.getD t 0) (certStabOrbitSizes.take t).sum
    certStabOrbitsText).toList

def smallArr (k : Nat) : Array Nat := hexTable 3 1782 (1782 * k) smallChainText

@[expose] def smallGenArrs : Array (Array Nat) := #[smallArr 0, smallArr 1]

@[expose] def smallStrongArrs : Array (Array Nat) :=
  #[smallArr 2, smallArr 3, smallArr 4, smallArr 5, smallArr 6, smallArr 7, smallArr 8,
    smallArr 9, smallArr 10, smallArr 11, smallArr 12, smallArr 13]

@[expose] def smallBaseNat : List Nat := [0, 1, 2, 3, 4, 8]

@[expose] def smallDerivs : Array (List Int) :=
  #[[], [], [1, -2, -2, 1, -2, 1, -2, 1, 2, 1, 2, 2, 1, 2, 1],
    [-2, 1, -2, -2, 1, -2, 1, -2, 1, -2, -2, 1, 2, 2, 1, 2, 1, 2, 1, 2, 2, 1, 2],
    [-3, -3, -3, 4, -3, -3, 4, 3, 3, 4, 3, 3, 3], [-3, -3, -3, 4, -3, 4, -3, 4, 3, 3, 3, 3, 4, 3],
    [6, 5], [-6, 5, 6, 5, 6, 6], [8, 8], [-7, 8, 8, 7], [-8, 7, 8, 7, 7, 7],
    [-11, -11, -7, -7, -8, -8, 7, 7, 7, 8, 7]]

def b0Arr : Array Nat := mtxArr suzP1782M1Text

def b1Arr : Array Nat := mtxArr suzP1782M2Text

def vArr : Array Nat := mtxArr suzd2P1782M1Text

def relabelArr : Array Nat := hexTable 4 22880 0 relabelText

def familySeed : List Nat := (hexTable 4 2080 0 familySeedText).toList

end CFSG.Sporadic.SuzOddCore
