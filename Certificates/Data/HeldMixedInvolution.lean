module

public import CFSG.Sporadic.HeldB.InnerCheckInputs
public import CFSG.LocalAnalysis.ComponentClassification.J2CoverAutNative

public section

namespace CFSG.Sporadic.HeldB.Mixed
open CFSG.Sporadic.HeldB CFSG.Sporadic.Schreier
  CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native
  CFSG.Monster.B.Co2.Native

@[expose] def generatorIndices : Array Nat := #[1,2,3,8]

@[expose] def mixedWords : List (List Int) :=
  [[1,2,3,2],
   [1,-4,1,2,4,4,3,4],
   [1,-4,1,2,1,-4,1,2],
   [1,4,1,-4,3,4,2],
   [3,-4,1,2,1,2,4,3],
   [3,-4,1,3,4,3],
   [2,1,3,-4,-4,2,1,4],
   [1,2,1,-4,-4,2,1,4]]

@[expose] def mixedCentralizerCheck (_ : Unit := ()) : Bool :=
  let small := generatorIndices.map fun j => heInnerSigma1.getD j #[]
  let smallInv := small.map (invCand 42)
  let gens := small.map (CFSG.ComponentClassification.J2Cover.arrTable 42)
  let gensInv := smallInv.map (CFSG.ComponentClassification.J2Cover.arrTable 42)
  let reps := mixedWords.map fun w =>
    CFSG.ComponentClassification.J2Cover.arrTable 42 (wordA 42 small smallInv w)
  let levels := levelTables heX1
  let tabs := filterProducts 42 allTrue levels (idT 42) []
  let invs := filterProducts 42 (ordTest 42 2) levels (idT 42) []
  let big := generatorIndices.map heInnerC1
  let bigInv := big.map (invCand 8330)
  let z := heT1Arr
  let lift := fun i : Nat => wordA 8330 big bigInv (mixedWords.getD i [])
  let fixed := fun r : Array Nat =>
    (List.range 8330).countP fun i => r[i]! == i
  reps.all (ordTest 42 2) &&
    repsOK 42 gens gensInv invs reps 128 &&
    ([1,4,5,6,7] : List Nat).all (fun i =>
      tabs.countP (commT 42 (reps.getD i (idT 42))) ==
        (if i == 1 then 512 else 128)) &&
    ([0,2] : List Nat).all (fun i =>
      let r := lift i
      fixed r == 42 && fixed (compA 8330 r z) == 42) &&
    (let r := lift 3; eqA 8330 (compA 8330 r r) z)

end CFSG.Sporadic.HeldB.Mixed
