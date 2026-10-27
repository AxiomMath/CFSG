module

public import CFSG.RankThree.PartTwo.Census.Carrier.G2ThreeData
public import Mathlib

public section

namespace Certificates.S5RowsG23

open CFSG.RankThree.PartTwo.Census.Carrier.G2Three

@[expose] def q8RelC (i j : List ℕ) : Bool :=
  let i2 := sq14 i
  mul14 i2 i2 == one14 && i2 != one14 && i2 == sq14 j && mul14 (mul14 i j) i == j

@[expose] def threeCycC (y i j : List ℕ) : Bool :=
  let jy := mul14 j y
  mul14 i y == mul14 y j && (jy == mul14 y (mul14 i j) || jy == mul14 y (mul14 j i))

@[expose] def g23RowsF4 (_ : Unit := ()) : Bool :=
  let es := elemsS
  let ex := elemsX
  es.all fun i => es.all fun j => !q8RelC i j || ex.any fun y => threeCycC y i j

end Certificates.S5RowsG23
