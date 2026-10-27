module

public import Certificates.Data.Odd87F3Check
public import CFSG.Sporadic.Schreier.MathieuOddCoreM11Data
public meta import Certificates.Data.Odd87F3Check
public meta import CFSG.Sporadic.Schreier.MathieuOddCoreM11Data
public meta import CFSG.Sporadic.Schreier.M11
public import CFSG.Sporadic.Schreier.M11
public import CFSG.Sporadic.Schreier.MathieuOddCoreCentral
public meta import CFSG.Sporadic.Schreier.MathieuOddCoreCentral
public meta import CFSG.Sporadic.Schreier.MathieuOddCoreWords
public import CFSG.Sporadic.Schreier.MathieuOddCoreWords

public section

namespace Certificates.Odd87F3.M11

open CFSG.Sporadic.Schreier CFSG.Sporadic.Mathieu

@[expose] def oddWords : List (List ℤ) :=
  [[-1, -2, -1, 2, -1, -2, -1, 2, -1, -2, -1, -2, -1, -2, -2, -1, -2, -2],
   [-1, 2, -1, -2, -2, -1, -2, -1, 2, 2, 1, -2, 1, 2, 1, 2]]

@[expose] def rows : List Row :=
  [⟨3, 2, 495, oddWords⟩, ⟨5, 1, 495, oddWords⟩, ⟨11, 1, 495, []⟩]

@[expose] def m11F3OK : Bool :=
  rowsOK 11 m11Certificate [m11gA, m11gB] (m11InvReps.getD 0 1) rows

end Certificates.Odd87F3.M11
