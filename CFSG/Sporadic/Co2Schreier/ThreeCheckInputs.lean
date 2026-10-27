module

public import CFSG.Sporadic.Co2Schreier.CoreCheckInputs
public import CFSG.Sporadic.Co2Schreier.SixCheckInputs
public meta import CFSG.Sporadic.Co2Schreier.CoreCheckInputs
public meta import CFSG.Sporadic.Co2Schreier.SixCheckInputs

public section

namespace CFSG.Sporadic.Co2Schreier

open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.Monster.B.Mathieu

@[expose] def p0Words : List (List ℤ) :=
  [[1, 2, 1, 2, 1, 2, -1, -1, 2, 1, 1, -2, 1, 2, -1, -2, -1, 2, -1, -1, 2, 1, 1, -2, -1, -1, -1,
      2, -1, -2, 1, 2, 1, 2, -1, -1, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, -1, -1, 2,
      1, 2, 1, 2, 2, 1, 2, -1, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1,
      1, 2, 1, 1, 1, 1, 1, 2],
    [-2, -2, -1, -1, -1, 2, -1, -2, -2, -1, -1, -2, -1, -1, -2, -1, 2, -1, -2, -2, 1, -2, 1, -2,
      -2, 1, -2, -1, 2, -1, -2, -1, -2, -1, -1, -1, 2, 1, 1, -2, 1, -2, 1, 1, 1, 2, -1, -2]]

@[expose] def p0Arrs : Array (Array ℕ) := (p0Words.map (wordArr cArrs)).toArray

@[expose] def enumP0 : LeftEnum := leftEnum p0Arrs 81

@[expose] def p0CentIdx (k : ℕ) : List ℕ :=
  (List.range 81).filter fun j => commA enumP0.elems[j]! enumP0.elems[k]!

@[expose] def p0MarkedIdx : List ℕ :=
  (List.range 81).filter fun k => decide (27 ≤ (p0CentIdx k).length)

@[expose] def qCentIdx56 : List ℕ :=
  (List.range 512).filter fun k => commA enumQ.elems[k]! enumP0.elems[56]!

@[expose] def p0SixOK (k : ℕ) (rows : List ℕ) : Bool :=
  allLt 6 fun j => sixImage enumP0.elems[k]! j == xorBits sixPacked (colBits rows j)

end CFSG.Sporadic.Co2Schreier
