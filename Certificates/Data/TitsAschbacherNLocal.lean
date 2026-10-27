module

public import Certificates.Data.TitsAschbacherE32
public import CFSG.Sporadic.Schreier.TitsCentralCheckInputs
public import CFSG.Sporadic.Schreier.TitsEnum

public section

namespace Certificates.TitsAschbacherNLocal

open CFSG.Sporadic.Schreier.Tits CFSG.Monster.B.Co2.Native Certificates.TitsAschbacherParrott
  Certificates.TitsAschbacherSecFour Certificates.TitsAschbacherE32 CFSG.Quasithin
  CFSG.Sporadic.Schreier

@[expose] def yWord : List ℕ := [2, 1, 3]

@[expose] def yArr (_ : Unit) : Array ℕ := nArr yWord

@[expose] def kWords : List (List ℕ) := [[1, 4], [1, 5], [4, 5]]

@[expose] def fA (m : ℕ) : Array ℕ := (fArrs ()).getD m #[]

@[expose] def inU11 (a : Array ℕ) : Bool := [0, 8, 16, 24].any fun m => eqA 1755 a (fA m)

@[expose] def commInU11 (x y : Array ℕ) : Bool :=
  [0, 8, 16, 24].any fun m => eqA 1755 (compA 1755 x y) (compA 1755 (compA 1755 (fA m) y) x)

@[expose] def commInU10 (y x : Array ℕ) : Bool :=
  (List.range 8).any fun i =>
    eqA 1755 (compA 1755 y x) (compA 1755 (compA 1755 (fA (4 * i)) x) y)

@[expose] def cTest (c : Array ℕ) : Bool :=
  !(commA c (vA 10) && commA c (vA 11) && commA c (vA 12)) ||
    [7, 9, 10, 11, 12].all fun j => commInU11 c (vA j)

@[expose] def tTest (yi y x : Array ℕ) : Bool :=
  notInT (compA 1755 (compA 1755 yi x) y) || inK x || inK (compA 1755 x piInv)

@[expose] def nlocCheck (_ : Unit) : Bool :=
  let y := yArr ()
  let yi := invCand 1755 y
  inK (compA 1755 titsPiArr titsPiArr) &&
    kWords.all (fun w => lettersIn 1 12 w && inK (vProd w)) &&
    eqA 1755 (compA 1755 (vProd [4, 5]) (vA 10))
      (compA 1755 (compA 1755 (vA 12) (vA 10)) (vProd [4, 5])) &&
    eqA 1755 (compA 1755 (vProd [1, 5]) (vA 10))
      (compA 1755 (compA 1755 (vA 11) (vA 10)) (vProd [1, 5])) &&
    (List.range 32).all (fun m => m % 8 == 0 ||
      kWords.any fun w => !commA (fA m) (vProd w)) &&
    (List.range 32).all (fun m => m % 4 == 0 ||
      kWords.any fun w => !commInU11 (fA m) (vProd w)) &&
    nLetters yWord && isInvA 1755 y yi && eqA 1755 (powA y 3) (idA 1755) &&
    !eqA 1755 y (idA 1755) && commA y (vA 10) && conjEqA y (vA 12) (vA 11) &&
    conjEqA y (compA 1755 (vA 11) (vA 12)) (vA 12) &&
    (List.range 32).all (fun m => m % 4 == 0 || !commInU10 y (fA m)) &&
    all5 1755 titsKLevels (fun k => cTest k && cTest (compA 1755 k titsPiArr)) &&
    all5 1755 titsSLevels (fun s => tTest yi y s && tTest yi y (compA 1755 s titsPiArr))

end Certificates.TitsAschbacherNLocal
