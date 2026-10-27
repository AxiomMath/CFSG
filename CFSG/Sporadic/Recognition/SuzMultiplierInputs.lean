module

public import CFSG.Certificates.CentralizerRelations
public import CFSG.LieType.Multipliers.TitsCheckInputs
public import CFSG.Sporadic.Presentation.SuzInputs
public import CFSG.Sporadic.SuzOddCore.Arrays
public import Certificates.Data.CFSGNative.Bridge.SuzGPL
public import CFSG.Sporadic.Recognition.SuzMultiplierData

public section

namespace CFSG.Sporadic.Recognition.SuzMultiplier

open CFSG.CosetTable CFSG.LieType.Multipliers CFSG.Sporadic.Presentation.Suz
  CFSG.Sporadic.Bridge.SuzGPL.Native CFSG.Sporadic.Schreier.Tits CFSG.Monster.B.Co2
  CFSG.Monster.B.Co2.Native CFSG.LieType.Multipliers.Tits CFSG.Sporadic.SuzOddCore

abbrev gcS : ℕ := TauCeti.SporadicName.Suz.presentation.generatorCount

abbrev suzW (c : List ℕ) : List (Fin gcS × Bool) := wordOfCodes gcS c

@[expose] def suzCommCodes : ℕ → List (List ℕ × List ℕ)
  | 0 => [([6], [4]), ([6], [4])]
  | 1 => [([0], [2]), ([0, 2, 4, 6, 4], [6])]
  | 2 => [([2, 0, 2], [0, 4]), ([2], [0])]
  | 3 => [([4, 2, 6, 8], [0, 4, 6, 4, 2, 0]), ([6, 8, 6, 4, 2, 6], [0, 2, 0, 2, 4])]
  | 4 => [([4, 6, 4, 2, 0], [8, 6, 4, 2, 6, 8]), ([0, 2, 0, 2, 6, 4], [6, 4, 2, 8, 6])]
  | 5 => [([2, 0, 2], [0, 10]), ([2], [0])]
  | _ => [([2, 0, 2], [0, 12]), ([2], [0])]

@[expose] def suzCommWord (i : Fin gcS) : List (Fin gcS × Bool) :=
  commWords ((suzCommCodes i.val).map fun p => (suzW p.1, suzW p.2))

abbrev suzCover : List (List (Fin gcS × Bool)) := coverWords R0 suzCommWord

abbrev suzCover1 := restrictWords (subsetOf _ [0, 1, 2, 3, 4, 6]) suzCover

abbrev suzCover2 := restrictWords (subsetOf _ [0, 1, 2, 3, 4]) suzCover1

@[expose] def suzR3 : List (Fin gcS × Bool) :=
  suzW [2, 10, 12, 2, 10, 12, 2, 10, 12, 2, 10, 12, 2, 10, 12]

@[expose] def suzGenArrs : Array (Array ℕ) := imgWords.map (wordArr 1782 #[b0Arr, b1Arr])

@[expose] def suzTabWords : List (List (Fin gcS × Bool)) :=
  R0 ++ (List.finRange gcS).map (fun i => (i, false) :: suzCommWord i) ++ [suzR3, suzW [6, 6]]

@[noinline, expose] def suzTabCheck : Bool :=
  allPermsOK 1782 #[b0Arr, b1Arr] && imgWords.size == 7 && imgWords.all (lettersOK 2) &&
    allPermsOK 1782 suzGenArrs &&
    suzTabWords.all (fun w => lettersOK gcS (zword w) &&
      eqA 1782 (wordArr 1782 suzGenArrs (zword w)) (idA 1782)) &&
    surjWords.size == 2 && lettersOK 7 surjWords[0]! && lettersOK 7 surjWords[1]! &&
    eqA 1782 (wordArr 1782 suzGenArrs surjWords[0]!) b0Arr &&
    eqA 1782 (wordArr 1782 suzGenArrs surjWords[1]!) b1Arr &&
    countBelow (fun x => (suzGenArrs[3]!)[x]! == x) 1782 == 42

@[expose] def suzRho0Arrs : Array (Array ℕ) :=
  Array.ofFn (n := 7) fun i => hexTable 4 5346 (5346 * i.val) suzRho0Text

@[noinline, expose] def suzRho0Check : Bool :=
  allPermsOK 5346 suzRho0Arrs &&
    suzCover.all (fun w => lettersOK gcS (zword w) &&
      eqA 5346 (wordArr 5346 suzRho0Arrs (zword w)) (idA 5346)) &&
    lettersOK gcS (zword suzR3) &&
    !eqA 5346 (wordArr 5346 suzRho0Arrs (zword suzR3)) (idA 5346) &&
    eqA 5346 (wordArr 5346 suzRho0Arrs (zword (suzR3 ++ suzR3 ++ suzR3))) (idA 5346)

@[expose] def suzRhoJ2Arrs : Array (Array ℕ) :=
  Array.ofFn (n := 5) fun i => hexTable 2 200 (200 * i.val) suzRhoJ2Text

@[noinline, expose] def suzRhoJ2Check : Bool :=
  allPermsOK 200 suzRhoJ2Arrs &&
    suzCover2.all (fun w => lettersOK 5 (zword w) &&
      eqA 200 (wordArr 200 suzRhoJ2Arrs (zword w)) (idA 200)) &&
    !eqA 200 (wordArr 200 suzRhoJ2Arrs [4, 4, 4, 4, 4, 4]) (idA 200)

end CFSG.Sporadic.Recognition.SuzMultiplier
