module

public import Certificates.Data.Odd87F3Check
public import CFSG.Sporadic.Schreier.MathieuOddCoreM22OuterData
public meta import Certificates.Data.Odd87F3Check
public meta import CFSG.Sporadic.Schreier.MathieuOddCoreM22OuterData
public meta import CFSG.Sporadic.Schreier.MathieuOddCoreM22
public import CFSG.Sporadic.Schreier.MathieuOddCoreM22
public meta import CFSG.Sporadic.Schreier.MathieuOddCoreModel
public import CFSG.Sporadic.Schreier.MathieuOddCoreModel
public import CFSG.Sporadic.Schreier.MathieuOddCoreOuter
public meta import CFSG.Sporadic.Schreier.MathieuOddCoreOuter

public section

namespace Certificates.Odd87F3.M22

open CFSG.Sporadic.Schreier CFSG.Sporadic.Mathieu

@[expose] def oddWordsInn_3 : List (List ℤ) :=
  [[-2, 1, -2, -2, -1, -2, -1, -2, -1, -2, -1, 2, 2, 1, -2, 1, 2, 2, 1, -2, 1, 2, 1, 2, 1, 2, 1, 2,
    2, 1, 2, 1, 2, 1, -2, 1, 2, -1, 2, -1, 2, -1, -2, -1, -2]]

@[expose] def oddWordsInn_5 : List (List ℤ) :=
  [[-2, 1, -2, -2, -1, -2, -1, -2, -1, -2, -1, 2, 2, 1, -2, 1, 2, 2, 1, -2, 1, 2, 1, 2, 1, 2, 1, 2,
    2, 1, 2, 1, 2, 1, -2, 1, 2, -1, 2, -1, 2, -1, -2, -1, -2],
   [1, 2, 1, -2, 1, 2, 1, -2, 1, 2, 1, 2, 2, 1, 2, 1, -2, 1, 2, 1, -2, -1, 2]]

@[expose] def rowsInn : List Row :=
  [⟨3, 2, 3, oddWordsInn_3⟩, ⟨5, 1, 3, oddWordsInn_5⟩, ⟨7, 1, 1, []⟩, ⟨11, 1, 1, []⟩]

@[expose] def oddWordsOut1_3 : List (List ℤ) :=
  [[-2, -2, -1, -2, -2, -2, 1, 2, 2, 1, 2, 1, 2, 1, 2, 1, -2, -2, -1, -2, -1, 2, -1, -2, -1, -2, -1,
    -2, -1, 2, -1, 2, -1, -2, -1, -2],
   [2, 2, 1, 2, 1, 2, 1, -2, 1, 1, -2, 1, 2, 2, 1, -2, -1, -2, -1, -2, -2, -1, -2]]

@[expose] def oddWordsOut1_5 : List (List ℤ) :=
  [[-2, -2, -1, -2, -2, -2, 1, 2, 2, 1, 2, 1, 2, 1, 2, 1, -2, -2, -1, -2, -1, 2, -1, -2, -1, -2, -1,
    -2, -1, 2, -1, 2, -1, -2, -1, -2],
   [2, 2, 1, 2, 1, 2, 1, -2, 1, 1, -2, 1, 2, 2, 1, -2, -1, -2, -1, -2, -2, -1, -2],
   [1, 2, 1, 2, 2, 1, 2, -1, 2, -1, 2, -1, -2, -1, 2, 1, 2, 1, 2, 2, 1, -2, 1, 2, 1, 2, 1, 2, 2, -1,
    -2, -1, 2, -1, 2, -1, 2, -1, -2, -1, -2]]

@[expose] def oddWordsOut1_11 : List (List ℤ) :=
  [[-2, -2, -1, -2, -2, -2, 1, 2, 2, 1, 2, 1, 2, 1, 2, 1, -2, -2, -1, -2, -1, 2, -1, -2, -1, -2, -1,
    -2, -1, 2, -1, 2, -1, -2, -1, -2],
   [2, 1, 2, 1, -2, 1, -2, -2, -1, -2, -1, 2, -1, 2, -1, -2, -2, -1, 2, -1, -2, -1, -2, 1, 2, 2, 1,
    2, 1, 2, 2, 1, -2, 1],
   [2, 1, 2, 1, 2, 1, -2, 1, -2, 1, 2, 2, 1, 2, 2, -1, 2, 1, 2, 1, -2, 1, -2, 1, -2, 1, -2, 1, -2,
    1, 2, 1, 2, 1, 2, 1, 2, 1, -2, 1, -2, 1],
   [2, 1, -2, 1, 2, 1, 2, 1, -2, 1, 2, 2, 1, -2, 1, 2, 2, 1, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 2, 1, -2,
    1, 2, 1, 2, 1, 2, 1, -2, -1, -2, -2, -1, 2, -1, 2, -1, -2, -1, -2],
   [2, 2, 1, 2, 1, 2, 1, -2, 1, 1, -2, 1, 2, 2, 1, -2, -1, -2, -1, -2, -2, -1, -2],
   [-1, 2, -1, 2, -1, -2, -1, -2, -2, -1, 2, -1, -2, -1, -2, -1, -2, -2, -1, 2, -1, 2, -1, -2, -2,
    1, 2, 2, 1, 2, 1, 1, -2, 1, 2, 1, 2, 1, 2]]

@[expose] def rowsOut1 : List Row :=
  [⟨3, 2, 5, oddWordsOut1_3⟩, ⟨5, 1, 5, oddWordsOut1_5⟩, ⟨7, 1, 1, []⟩, ⟨11, 1, 5, oddWordsOut1_11⟩]

@[expose] def oddWordsOut2_3 : List (List ℤ) :=
  [[2, -1, -2, -1, -2, -2, -1, -2, -1, -2, -2, -1, -2, -2, -2, -1, -2, -1, -2, -1, -2, -2, -1, 2,
    -1, 2, -1, -2, -2],
   [2, 2, 1, 2, 1, 2, 2, 1, -2, 1, 2, 1, 2, 1, 2, 2, -1, -2, -1, 2, 1, 2, 1, -2, 1, 2, 1, -2, 1, -2,
    1, 2, 2, 1, 2, 1, -2, 1, 2, 2, -1, -2, -2, -1, -2],
   [-1, 2, -1, 2, -1, -2, -1, 2, 1, 2, -1, -2, -1, -2, -1, -2, -1, 2, -1, -2, -2, -1, -2, -2, 1, -2,
    1, 2, 2, 1, 2, 1, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 2, 2, -1, -2, -2, -1, -2]]

@[expose] def rowsOut2 : List Row :=
  [⟨3, 2, 3, oddWordsOut2_3⟩, ⟨5, 1, 1, []⟩, ⟨7, 1, 1, []⟩, ⟨11, 1, 1, []⟩]

@[expose] def m22F3OK : Bool :=
  rowsOK 22 m22Certificate [m22gA, m22gB] (m22InvReps.getD 0 1) rowsInn &&
  rowsOK 22 m22Certificate [m22gA, m22gB] (m22OutReps.getD 0 1) rowsOut1 &&
  rowsOK 22 m22Certificate [m22gA, m22gB] (m22OutReps.getD 1 1) rowsOut2

end Certificates.Odd87F3.M22
