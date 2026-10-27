module

public import Certificates.Data.Odd87F3Check
public import CFSG.Sporadic.Schreier.MathieuOddCoreM12Outer
public meta import Certificates.Data.Odd87F3Check
public meta import CFSG.Sporadic.Schreier.MathieuOddCoreM12Outer

public section

namespace Certificates.Odd87F3.M12

open CFSG.Sporadic.Schreier CFSG.Sporadic.Mathieu

@[expose] def repWordInn1 : List ℤ :=
  [2, -1, -2, -1, -2, -1, -2, -1, 2, -1, 2, -1, -2, -1, 2, -1, -2, -1, -2, -1, -2, -1, 2, -1, 2, -1,
   2, -1, 2, -1, 2, 2, 1, -2, 1, -2, 1, -2, 1, 2, 1, -2, 1, 2, 1, 2, 2, -1, -2, -1, 2, -1, -2, -1]

@[expose] def repWordInn2 : List ℤ :=
  [-2, -1, -1, -2, -1, 2, -1, 2, 2, 1, 2, 1, -2, 1, 2, 1, 2, 1, -2, 1, -2, 1, 2, 2, -1, -2, -1, 2,
   -1, -2, -1, -1, -2, -1, 2, -1, -2, -1]

@[expose] def innerReps : List (Equiv.Perm (Fin 24)) :=
  [evalCodes [m12A1, m12B1] repWordInn1, evalCodes [m12A1, m12B1] repWordInn2]

@[expose] def oddWordsInn1_3 : List (List ℤ) :=
  [[-1, -2, -1, 2, -1, -2, -1, 2, -1, -2, -1, -2, -1, -2, -2, 1, -2, 1, 2, 1, 2, 1, 2, 2, -1, -2,
    -1, 2, -1, -2, -1, -2],
   [-2, -1, -1, -2, -1, -2, -1, 2, -1, 2, -1, -2, -1, 2, -1, 2, -1, 2, -1, 2, -1, -2, -1, -2, -1,
    -2, -1, -2, -1, -2, -1, 2, -1, -2, -1, 2, -1, -2, -1, -2]]

@[expose] def oddWordsInn1_5 : List (List ℤ) :=
  [[-1, -2, -1, 2, -1, -2, -1, 2, -1, -2, -1, -2, -1, -2, -2, 1, -2, 1, 2, 1, 2, 1, 2, 2, -1, -2,
    -1, 2, -1, -2, -1, -2],
   [1, 2, 1, -2, 1, 2, 1, -2, -2, 1, -2, 1, 2, 1, -2, 1, 2, 1, 2, 1, 2, 1, -2, 1, 2, 1, 2, 1, 2, 1,
    -2, 1, 2, 1, 2, 1, -2, 1]]

@[expose] def rowsInn1 : List Row :=
  [⟨3, 3, 3, oddWordsInn1_3⟩, ⟨5, 1, 3, oddWordsInn1_5⟩, ⟨11, 1, 1, []⟩]

@[expose] def oddWordsInn2_3 : List (List ℤ) :=
  [[1, 2, 1, -2, 1, 2, 1, 1, 2, 1, -2, 1, 2, 1, -2, 1, 2, 1, 2, 1, 2, 1, -2, 1, 2, 1, -2, 1, -2, -1,
    -2, -1, -2, -1, -2, -1, -2, -1, 2, 2, 1]]

@[expose] def oddWordsInn2_5 : List (List ℤ) :=
  [[-1, -2, -2, 1, 2, 1, 2, 1, 2, 1, -2, 1, 2, -1, -2, -1, -2, -1, 2, -1, -2, -1, 2, -1, -2, -1, -1,
    -2, -1, 2, -1, -2, -1]]

@[expose] def rowsInn2 : List Row :=
  [⟨3, 3, 5, oddWordsInn2_3⟩, ⟨5, 1, 3, oddWordsInn2_5⟩, ⟨11, 1, 1, []⟩]

@[expose] def oddWordsSig_3 : List (List ℤ) :=
  [[-2, -1, 2, -1, -2, -1, 2, -1, -2, -1, -2, -1, -2, -1, -1, -2, -1, -2, -1, -2, -1, 2, -1, -2, -1,
    2, -1, 2, -1, 2, -1],
   [-1, -2, -1, 2, 2, -1, -2, -1, -2, -1, 2, -1, -2, -1, -2, -1, -2, -1, -2, -1, -2, -1, 2, -1, -2,
    -1, 2, -1, -2, -1, -1, -2, -1, 2, -1, -2]]

@[expose] def oddWordsSig_5 : List (List ℤ) :=
  [[-1, -2, -1, 2, 2, -1, -2, -1, -2, -1, 2, -1, -2, -1, -2, -1, -2, -1, -2, -1, -2, -1, 2, -1, -2,
    -1, 2, -1, -2, -1, -1, -2, -1, 2, -1, -2]]

@[expose] def oddWordsSig_11 : List (List ℤ) :=
  [[1, 2, 1, -2, 1, 2, 1, -2, -2, -1, -2, -1, -2, -1, 2, -1, -2, -1, 2, -1, 2, -1, 2, 2, -1, -2, -1,
    2, -1, -2],
   [-2, -1, 2, 2, -1, -2, -1, -2, -1, 2, -1, -2, -1, -2, -1, -2, -1, -2, -1, -2, -1, 2, -1, -2, -1,
    2, -1, -2, -1, -1, -2, -1, 2, -1, -2]]

@[expose] def rowsSig : List Row :=
  [⟨3, 3, 5, oddWordsSig_3⟩, ⟨5, 1, 5, oddWordsSig_5⟩, ⟨11, 1, 3, oddWordsSig_11⟩]

@[expose] def m12F3OK : Bool :=
  coverOK 24 m12D m12A1 m12B1 1 innerReps 1000 &&
  rowsOK 24 m12D [m12A1, m12B1] (evalCodes [m12A1, m12B1] repWordInn1) rowsInn1 &&
  rowsOK 24 m12D [m12A1, m12B1] (evalCodes [m12A1, m12B1] repWordInn2) rowsInn2 &&
  rowsOK 24 m12D [m12A1, m12B1] m12Sigma rowsSig

end Certificates.Odd87F3.M12
