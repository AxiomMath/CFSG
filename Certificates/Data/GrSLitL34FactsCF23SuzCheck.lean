module

public import CFSG.Sporadic.SuzOddCore.InvTCheckInputs
public import CFSG.LieType.Multipliers.L34Data
public import CFSG.Certificates.CosetTableShort
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.Open.Defs

public section

namespace CFSG.ComponentClassification.GSThmB.CF23L34

open CFSG.Sporadic.SuzOddCore CFSG.Monster.B.Co2.Native CFSG.LieType.Multipliers.L34

@[expose] def suzFusText : String := include_str "GrSLitL34FactsCF23Suz.txt"

def suzY1Arr : Array Nat := hexTable 3 1782 0 suzFusText

def suzY2Arr : Array Nat := hexTable 3 1782 1782 suzFusText

def suzMArr : Array Nat := hexTable 3 1782 3564 suzFusText

@[expose] def suzGens : Array (Array Nat) := #[suzY1Arr, suzY2Arr]

@[expose] def suzGensInv : Array (Array Nat) := suzGens.map (invCand 1782)

@[expose] def evalFW (n : Nat) (g gi : Array (Array Nat)) : List (Fin 2 × Bool) → Array Nat
  | [] => idA n
  | (i, b) :: w => compA n (if b then g[i.val]! else gi[i.val]!) (evalFW n g gi w)

@[noinline, expose] def suzFusOK : Bool :=
  isInvA 1782 suzY1Arr suzGensInv[0]! && isInvA 1782 suzY2Arr suzGensInv[1]! &&
    isInvA 1782 suzMArr (invCand 1782 suzMArr) && inM suzY1Arr && inM suzY2Arr && inM suzMArr &&
    commutesA suzY1Arr (tArr 0) && commutesA suzY2Arr (tArr 0) &&
    (coverWs ++ [zOne, zTwo, zThree]).all (fun w =>
      eqA 1782 (evalFW 1782 suzGens suzGensInv w) (idA 1782)) &&
    eqA 1782 (compA 1782 (compA 1782 suzMArr (tArr 0)) (invCand 1782 suzMArr))
      (compA 1782 (tArr 0) suzY1Arr) &&
    !(eqA 1782 suzY1Arr (idA 1782))

end CFSG.ComponentClassification.GSThmB.CF23L34
