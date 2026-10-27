module

public import CFSG.Sporadic.Schreier.RuArrays
public import CFSG.Sporadic.Schreier.RuCore
public meta import CFSG.Sporadic.Schreier.RuArrays
public meta import CFSG.Sporadic.Schreier.RuCore
public meta import CFSG.Sporadic.Schreier.RuEnum
public import CFSG.Sporadic.Schreier.RuEnum
public meta import Mathlib.GroupTheory.Schreier
public import Mathlib.GroupTheory.Schreier

public section

namespace CFSG.Quasithin.F7Two

open CFSG.Monster.B.Co2.Native CFSG.Sporadic.RuSchreier

@[expose] def ruCommA (y x yi xi : Array Nat) : Array Nat :=
  compA 4060 (compA 4060 (compA 4060 y x) yi) xi

@[expose] def ruSevenChk (c : Array Nat) : Bool :=
  eqA 4060 (powA 4060 c 7) (idA 4060) && !eqA 4060 c (idA 4060)

@[expose] def ruInvChk (_ : Unit) : Bool :=
  ruSevenChk (ruCommA ruA0A ruA1A (ruInv ruA0A) (ruInv ruA1A)) &&
    ruSevenChk (ruCommA (compA 4060 ruA1A ruA1A) ruA0A
      (compA 4060 (ruInv ruA1A) (ruInv ruA1A)) (ruInv ruA0A))

end CFSG.Quasithin.F7Two
