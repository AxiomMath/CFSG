module

public import CFSG.Sporadic.Schreier.MathieuOddCoreClasses
public import CFSG.Sporadic.Schreier.M22Data

public section

namespace CFSG.Quasithin.B45Mat.M22

open CFSG.Sporadic.Schreier CFSG.Sporadic.Mathieu CFSG.Sporadic.Schreier.Native

@[expose] def invWord (w : List ℤ) : List ℤ := (w.map fun z => -z).reverse

@[expose] def word3 : List ℤ := [1, 2, 1, 2, 2, 2, 1, 2, 2, 2, 1, 2]

@[expose] def word5 : List ℤ := [2, 2, 1]

@[expose] def word7 : List ℤ := [-2, -2, 1, -2, 1, -2, 1, -2, 1, 2, 1]

@[expose] def word11 : List ℤ := [1, 2]

@[expose] def oddReps3 : List (Equiv.Perm (Fin 22)) := [evalCodes [m22gA, m22gB] word3]

@[expose] def oddReps5 : List (Equiv.Perm (Fin 22)) := [evalCodes [m22gA, m22gB] word5]

@[expose] def oddReps7 : List (Equiv.Perm (Fin 22)) :=
  [evalCodes [m22gA, m22gB] word7, evalCodes [m22gA, m22gB] (invWord word7)]

@[expose] def oddReps11 : List (Equiv.Perm (Fin 22)) :=
  [evalCodes [m22gA, m22gB] word11, evalCodes [m22gA, m22gB] (invWord word11)]

end CFSG.Quasithin.B45Mat.M22
