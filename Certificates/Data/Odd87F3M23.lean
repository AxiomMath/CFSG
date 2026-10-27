module

public import Certificates.Data.Odd87F3Check
public import CFSG.Sporadic.Schreier.MathieuOddCoreM23Data
public meta import Certificates.Data.Odd87F3Check
public meta import CFSG.Sporadic.Schreier.MathieuOddCoreM23Data
public import CFSG.Sporadic.M23.M23Group
public meta import CFSG.Sporadic.M23.M23Group
public meta import CFSG.Sporadic.Mathieu.Simple
public import CFSG.Sporadic.Mathieu.Simple
public import CFSG.Sporadic.Schreier.M23Base
public meta import CFSG.Sporadic.Schreier.M23Base
public import CFSG.Sporadic.Schreier.M23CheckBase
public meta import CFSG.Sporadic.Schreier.M23CheckBase
public import CFSG.Sporadic.Schreier.MathieuOddCoreCentral
public meta import CFSG.Sporadic.Schreier.MathieuOddCoreCentral
public import CFSG.Sporadic.Schreier.MathieuOddCoreWords
public meta import CFSG.Sporadic.Schreier.MathieuOddCoreWords
public import CFSG.Sporadic.Schreier.Outer
public meta import CFSG.Sporadic.Schreier.Outer

public section

namespace Certificates.Odd87F3.M23

open CFSG.Sporadic.Schreier CFSG.Sporadic.Mathieu

@[expose] def oddWords3 : List (List ℤ) :=
  [[2, 1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 1, -2, -1, 2, -1, 2, -1, 2, -1, -2, -1, -2, -1, 2, -1, -2, -1,
    -2, -1, -2, -2, -1, 2, -1, -2, -1, -2, -2, -1, 2, -1, -2, 1, -2, 1, 2, 1, 2, 1, 2, 2, 1, -2, 1,
    -2, 1, -2, -1, -2, 1, 2, 1, 2, 1, 2, 1],
   [-2, -1, -2, -1, -2, -1, -2, -1, 2, -1, -2, -1, -2, -2, -1, 2, -1, -1, 2, -1, -2, -1, -2, -1, 2,
    -1, 2, -1, 2, -1, -2, -2, -1, -2, -2, -1, -2, -1, -2, -2, -1, -1, -2, -1, -2, -1, -2, -2, -1,
    -2, -1, 2, -1, 2, -1, -2, -2, -1, 2, 2, -1, -2, -1, 2, -1, -2, -1, 2, -1, -2, -1, 2, -1, -2, -2,
    -1]]

@[expose] def oddWords5 : List (List ℤ) :=
  [[-2, -1, -2, -1, -2, -1, -2, -1, 2, -1, -2, -1, -2, -2, -1, 2, 2, 2, 1, 2, -1, -2, -1, 2, 1, -2,
    1, 2, 1, 2, 1, 2, 1, -2, 1, 2, 2, 1, 2, 1, 2, 2, 1, -2, 1, -2, 1, -2, 1, 2, 2, -1, -2, -1, 2,
    -1, -2, -2, -1, 2, -1, -2, -1, 2, -1, -2, -2, -1],
   [-2, 1, 2, 2, 1, -2, 1, -2, 1, -2, 1, -2, 1, 2, 2, 1, 2, 1, 2, 1, -2, 1, -2, 1, 2, 1, -2, 1, -2,
    1, 2, 1, 2, 1, 2, 1, 2, 1, -2, 1, -2, 1, 2, 1, 2, 2, 1, 2, 1, -2, 1, 2, 1, -2, 1, 2, 2, 1, 2,
    -1, 2],
   [2, 2, 1, -2, 1, 2, 1, -2, -1, 2, -1, -2, -2, -1, 2, -1, -2, -1, 2, -1, 2, -1, -2, -1, -2, -2, 1,
    -2, 1, -2, 1, -2, 1, 2, 2, 1, 2, 1, -2, 1, 2, 2, 1, 2, 1, 2, 2, 1, -2, -1, -2, -1, -2, -2, -1,
    2, -1, -2, -1, 2, -1, 2, -1, -2, -1, -1, -2, -1, -2, -1, -2, -1, 2, -1, -2, -1, -2, -2, -1, 2,
    -1, 2]]

@[expose] def rows : List Row :=
  [⟨3, 2, 3, oddWords3⟩, ⟨5, 1, 21, oddWords5⟩, ⟨7, 1, 1, []⟩, ⟨11, 1, 1, []⟩, ⟨23, 1, 1, []⟩]

@[expose] def m23F3OK : Bool :=
  rowsOK 23 m23Certificate [m23PermA, m23PermB] (m23InvReps.getD 0 1) rows

end Certificates.Odd87F3.M23
