module

public import Certificates.Data.Odd87F3Check
public import CFSG.Sporadic.SmallOddCore.J2Data
public import CFSG.LocalAnalysis.ComponentClassification.J2CoverAutNative
public import CFSG.Sporadic.Schreier.PairJ2CheckInputs
public meta import Certificates.Data.Odd87F3Check
public meta import CFSG.Sporadic.SmallOddCore.J2Data
public meta import CFSG.LocalAnalysis.ComponentClassification.J2CoverAutNative
public meta import CFSG.Sporadic.Schreier.PairJ2CheckInputs

public section

namespace Certificates.Odd87F3.J2

open CFSG.Sporadic.Schreier CFSG.Sporadic.SmallOddCore CFSG.Sporadic.Th.Native CFSG.ComponentClassification.J2Cover

@[expose] def j2Tss : List (List Table) :=
  chainTables 315 CFSG.Sporadic.Schreier.PairNative.j2StrongArrs CFSG.Sporadic.Schreier.PairJ2.baseArr

@[expose] def rowAt (i : Fin 3) : ClassRow :=
  j2Rows[i.val]'(by have h : j2Rows.length = 3 := by decide
                    omega)

@[expose] def oddWordsR1_3 : List (List ℤ) :=
  [[3, 3, -2, -3, -2],
   [1, 2, 1, 2, 1, 3, 2]]

@[expose] def oddWordsR1_7 : List (List ℤ) :=
  [[3, 3, -2, -3, -2],
   [1, 2, 1, 2, 1, 3, 2]]

@[expose] def rowsR1 : List Row :=
  [⟨3, 3, 3, oddWordsR1_3⟩, ⟨5, 2, 1, []⟩, ⟨7, 1, 3, oddWordsR1_7⟩]

@[expose] def oddWordsR2_3 : List (List ℤ) :=
  [[-5, -2, 5, 2]]

@[expose] def oddWordsR2_5 : List (List ℤ) :=
  [[-5, -2, 5, 2],
   [-4, 3, 2, -4],
   [-3, -4, 3, 2, -1, -4],
   []]

@[expose] def oddWordsR2_7 : List (List ℤ) :=
  [[-2, 4, 3, 1]]

@[expose] def rowsR2 : List Row :=
  [⟨3, 3, 3, oddWordsR2_3⟩, ⟨5, 2, 3, oddWordsR2_5⟩, ⟨7, 1, 5, oddWordsR2_7⟩]

@[expose] def oddWordsR3_3 : List (List ℤ) :=
  [[-2, -4, -2, -1, -2, -1, 3, 2],
   [-2, -3, 1, 4, 3, 3, 4],
   [-1, -4, -4, -1]]

@[expose] def oddWordsR3_5 : List (List ℤ) :=
  [[-3, -2, 4],
   [3, 2, 1, 4, 3, 2, 3]]

@[expose] def rowsR3 : List Row :=
  [⟨3, 3, 3, oddWordsR3_3⟩, ⟨5, 2, 5, oddWordsR3_5⟩, ⟨7, 1, 1, []⟩]

@[expose] def j2F3OK : Bool :=
  ((List.finRange 3).all fun i => permOK 315 (rowAt i).rep && (rowAt i).centGens.all (permOK 315)) &&
  rowsOKT 315 604800 j2Tss (rowAt 0).centGens (rowAt 0).rep rowsR1 &&
  rowsOKT 315 604800 j2Tss (rowAt 1).centGens (rowAt 1).rep rowsR2 &&
  rowsOKT 315 604800 j2Tss (rowAt 2).centGens (rowAt 2).rep rowsR3

end Certificates.Odd87F3.J2
