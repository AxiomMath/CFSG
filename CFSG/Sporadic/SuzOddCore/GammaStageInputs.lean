module

public import CFSG.Sporadic.SuzOddCore.GammaCheckInputs
public import Certificates.Data.CFSGNative.FischerOddCore.Checks

public section

namespace CFSG.Sporadic.SuzOddCore

open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.Sporadic.FischerOddCore.Native

@[expose] def gammaE0 : Array Nat := colourT 22880 gammaNbr (idA 22880) [0] 2

@[expose] def gammaWords : List (List Nat) := [[], [0], [1, 1], [0, 1, 1]]

@[expose] def gammaWordArr (w : List Nat) : Array Nat :=
  w.foldr (fun k u => compA 22880 (certArr k) u) (idA 22880)

@[expose] def gammaMover (s : Nat) : Array Nat := gammaWordArr (gammaWords.getD s [])

@[expose] def gammaBaseCol (c u e : Array Nat) : Array Nat :=
  Array.ofFn (n := 22880) fun v => (c[v.val]! % cmod * 1000003 + e[u[v.val]!]!) % cmod

@[expose] def gammaRounds : List Nat := [0, 2, 1, 2]

@[expose] def gammaStage : Nat → Array Nat
  | 0 => Array.replicate 22880 1
  | s + 1 => refineT 22880 gammaNbr (idA 22880)
      (gammaBaseCol (gammaStage s) (gammaMover s) gammaE0) (gammaRounds.getD s 0)

@[expose] def gammaStagesOK : Bool :=
  allLt 4 (fun s => (gammaMover s)[s]! == 0) &&
    decide (cellCount 22880 (gammaStage 1) (gammaStage 1)[1]! ≤ 8505) &&
    decide (cellCount 22880 (gammaStage 2) (gammaStage 2)[2]! ≤ 1152) &&
    decide (cellCount 22880 (gammaStage 3) (gammaStage 3)[3]! ≤ 4) &&
    colInj 22880 (gammaStage 4)

end CFSG.Sporadic.SuzOddCore
