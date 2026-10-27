module

public import CFSG.Sporadic.Schreier.RuCheckInvInputs
public import CFSG.Sporadic.Schreier.RuCheckCentersInputs

public section

namespace CFSG.Sporadic.RuSchreier.RuB1

open CFSG.Sporadic.RuSchreier CFSG.Monster.B.Co2.Native CFSG.Certificates.Native

@[expose] def scWords : List (List ℤ) :=
  [[1, 1], [-1, -1], [-1], [1], [-2, 1, 4, 1], [3, 4, 1], [3, 4, -1, -1], [3, 4, -1],
   [-2, 1, 4, -1], [-4, -2, 1, 4, 1], [-2, 1, 4, 1, 1], [3, 4, 1, 1]]

@[expose] def scGens : Array (Array ℕ) := #[ruC0A, ruC1A, ruNs0A, ruNs1A]

@[expose] def scGensInv : Array (Array ℕ) :=
  #[ruInv ruC0A, ruInv ruC1A, ruInv ruNs0A, ruInv ruNs1A]

@[expose] def scL (w : List ℤ) : Array ℕ := wordA 4060 scGens scGensInv w

@[expose] def scConjE (w : List ℤ) : Array (Array ℕ) := ruEArr.map (ruConjA (scL w))

@[expose] def scEs : List (Array (Array ℕ)) := scWords.map scConjE

@[expose] def scComm (t u : Array ℕ) : Bool := eqA 4060 (compA 4060 t u) (compA 4060 u t)

@[expose] def scTest (t : Array ℕ) : Bool :=
  !eqA 4060 (compA 4060 t t) (idA 4060) || allLt 7 (fun j => scComm t ruEArr[j]!) ||
    scEs.any fun E => allLt 7 fun j => scComm t E[j]!

@[noinline, expose] def ruB1SCCheck : Bool :=
  ruEArr.size == 7 && scWords.all (lettersOK 4) &&
    scWords.all (fun w => isInvA 4060 (scL w) (ruInv (scL w))) &&
    scEs.all (fun E => allLt 7 fun j =>
      siftA 4060 ruLevS (ruBaseArr 4060 ruS4060ChainBase) 0 E[j]!) &&
    all2 4060 ruLevS scTest

end CFSG.Sporadic.RuSchreier.RuB1
