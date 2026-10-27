module

public import CFSG.Sporadic.Schreier.MathieuOddCoreClasses
public import CFSG.Sporadic.Schreier.M12Data

public section

namespace CFSG.Quasithin.B45Mat.M12

open CFSG.Sporadic.Schreier CFSG.Sporadic.Mathieu CFSG.Sporadic.Schreier.Native

@[expose] def oddReps3 : List (Equiv.Perm (Fin 12)) :=
  [evalCodes [m12gA, m12gB] [2, 2, 1, 2, 1, 2, 2, 1, 2, 1], evalCodes [m12gA, m12gB] [2]]

@[expose] def oddReps5 : List (Equiv.Perm (Fin 12)) :=
  [evalCodes [m12gA, m12gB] [2, 2, 1, 2, 2, 1, 2, 1, 2, 1]]

@[expose] def oddReps11 : List (Equiv.Perm (Fin 12)) :=
  [evalCodes [m12gA, m12gB] [2, 2, 1], evalCodes [m12gA, m12gB] [2, 1]]

end CFSG.Quasithin.B45Mat.M12
