module

public import Certificates.Data.GH74.BTFinCk
public import CFSG.Sporadic.Schreier.M12
public import CFSG.Sporadic.Schreier.MathieuOddCoreCentral
public meta import Certificates.Data.GH74.BTFinCk
public meta import CFSG.Sporadic.Schreier.M12
public meta import CFSG.Sporadic.Schreier.MathieuOddCoreCentral
public meta import CFSG.Sporadic.Schreier.MathieuOddCoreWords
public import CFSG.Sporadic.Schreier.MathieuOddCoreWords

public section

namespace Certificates.BTFinCk.M12

open CFSG.Sporadic.Schreier CFSG.Sporadic.Mathieu CFSG.Sporadic.Th.Native
  CFSG.Sporadic.Schreier.Native CFSG.Certificates

@[expose] def gT : Array Table := pairTables m12gA m12gB

@[expose] def gIT : Array Table := pairTables m12gA⁻¹ m12gB⁻¹

@[expose] def rows : List (ℕ × List ℤ × ℕ × ℕ × List (List ℤ)) :=
  [(3, [2], 2640, 36,
      [[2], [1, 2, 1, 2, 1, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 1, 2, 1, 2, 1],
        [1, 2, 1, 2, 2, 1, 2, 1, 2, 1, 2, 2, 1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 2, 1, 2, 1, 2, 2, 1,
          2, 1, 2, 1, 2, 2, 1]]),
    (3, [1, 2, 1, 2, 2, 1, 2, 1, 2, 2], 1760, 54,
      [[1, 2, 1, 2, 2], [2, 2, 1, 2, 1, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 1, 2, 1, 2],
        [1, 2, 2, 1, 2, 1, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1]]),
    (5, [1, 2, 1, 2, 1, 2, 2, 1, 2, 2], 9504, 10,
      [[1, 2, 1, 2, 1, 2, 2, 1, 2, 2],
        [1, 2, 2, 1, 2, 1, 2, 1, 2, 2, 1, 2, 2, 1, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 1, 2, 1, 2, 2, 1,
          2, 2, 1, 2, 1, 2, 1, 2, 2, 1, 2]]),
    (11, [1, 2], 8640, 11, [[1, 2]]),
    (11, [1, 2, 2], 8640, 11, [[2, 1]])]

@[expose] def repsOf (p : ℕ) : List (Equiv.Perm (Fin 12)) :=
  (rows.filter fun r => r.1 == p).map fun r => evalCodes [m12gA, m12gB] r.2.1

@[expose] def rowOK (r : ℕ × List ℤ × ℕ × ℕ × List (List ℤ)) : Bool :=
  let a := evalCodes [m12gA, m12gB] r.2.1
  let cg := r.2.2.2.2.map (evalCodes [m12gA, m12gB])
  ordTest 12 r.1 (toTable a) && cg.all (fun h => commT 12 (toTable h) (toTable a)) &&
    (conjClosure 12 gT gIT (toTable a) 20000).1.size == r.2.2.1 &&
    r.2.2.1 * r.2.2.2.1 == 95040 && centFourOK 12 (cg.map toTable) (toTable a) r.2.2.2.1 1000 0

@[expose] def m12OddCk : Bool :=
  rows.all rowOK && [3, 5, 11].all fun p =>
    repsOK 12 gT gIT (cosetOrderTables m12Certificate 1 p) ((repsOf p).map toTable) 20000

end Certificates.BTFinCk.M12
