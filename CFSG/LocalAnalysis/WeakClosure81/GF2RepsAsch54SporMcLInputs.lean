module

public import CFSG.ClassicalInvolution.SmallCases.Sporadic.McLCheckInputs
public meta import CFSG.ClassicalInvolution.SmallCases.Sporadic.McLCheckInputs

public section

namespace CFSG.LocalAnalysis.WeakClosure81.SporMcL

open CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native CFSG.Sporadic.Th.Native
  CFSG.Sporadic.Schreier.Native CFSG.Certificates.Native CFSG.Sporadic.Schreier.Co3.Native
  CFSG.ClassicalInvolution.McLData CFSG.ClassicalInvolution.McLProof

@[expose] def alphaWordS : List Nat := [1, 1, 1, 1]

@[expose] def uWord : List Nat := [2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1]

@[expose] def uTbl : Table := wordTbl 275 sgens uWord

@[expose] def vgens : List Table := [Ta, uTbl]

@[expose] def vElems : List Table := [idT 275, Ta, uTbl, compT 275 Ta uTbl]

@[expose] def commTbl (x t : Table) : Table :=
  compT 275 (compT 275 (compT 275 x t) (invT 275 x)) (invT 275 t)

@[expose] def inZ (c : Table) : Bool := tblEq 275 c (idT 275) || tblEq 275 c Ta

@[expose] def z2Test (E : Array Table) (x : Table) : Bool := E.all fun t => inZ (commTbl x t)

@[expose] def z2Count (E : Array Table) : Nat := E.toList.countP (z2Test E)

@[expose] def hWords : List (List Nat) :=
  [[1, 2, 2, 2, 2, 2, 2, 2, 2, 1, 2, 2, 2, 2, 2, 2, 2, 2, 1, 2, 2, 2, 2, 1, 2, 2, 2, 2, 2, 2, 2,
    2, 1, 2, 2, 2, 2, 2, 2, 2, 2, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1, 2, 2, 1, 2, 1, 2, 2, 2,
    2, 2, 2, 2, 2, 1, 2, 1, 2, 2, 2, 2, 2, 2, 2, 2, 1, 2, 2, 1, 2, 2, 2, 1, 2, 2, 2, 2, 1, 2, 1, 2,
    1, 2, 1, 2, 1, 2, 2, 2, 2, 1, 2, 1, 2, 1, 2, 2, 2, 2, 2, 2, 2, 2, 1, 2, 2, 1, 2, 2, 2, 2, 1, 2,
    2, 2, 2, 2, 2, 2, 2, 1, 2, 2, 2, 2, 1, 2, 2, 2, 2, 1, 2, 2, 2, 2, 1, 2, 2, 2, 2, 1, 2],
   [1, 2, 1, 2, 2, 2, 2, 2, 2, 2, 2, 1, 2, 1, 2, 2, 2, 2, 1, 2, 2, 1, 2, 2, 2, 2, 1, 2, 2, 2, 2,
    1, 2, 2, 2, 2, 1, 2, 1, 2, 2, 2, 2, 1, 2, 2, 2, 2, 2, 2, 2, 2, 1, 2, 2, 2, 2, 2, 2, 2, 2, 1, 2,
    2, 1, 2, 2, 2, 1, 2, 2, 1, 2, 2, 2, 2, 1, 2, 2, 1, 2, 2, 2, 2, 2, 2, 2, 2, 1, 2, 1, 2, 2, 2, 2,
    1, 2, 1, 2, 2, 2, 2, 2, 2, 2, 2, 1, 2, 2, 1, 2, 1, 2, 2, 2, 2, 2, 2, 2, 2, 1, 2, 2, 2, 2, 1, 2,
    2, 2, 2, 2, 2, 2, 2, 1, 2, 2, 1, 2, 1, 2, 1, 2, 2, 2, 2, 2, 2, 2, 2, 1, 2, 2, 1, 2],
   [2, 2, 2, 2, 1, 2, 1, 2, 2, 2, 2, 2, 2, 2, 2, 1, 2, 2, 1, 2, 1, 2, 1, 2, 2, 1, 2, 2, 2, 2, 2,
    2, 2, 2, 2, 2, 2, 2, 1, 2, 2, 1, 2, 2, 2, 2, 1, 2, 1, 2, 2, 2, 2, 2, 2, 2, 2, 1, 2, 2, 2, 2, 1,
    2, 1, 2, 2, 2, 2, 1, 2, 2, 1, 2, 2, 2, 2, 2, 2, 2, 2, 1, 2, 2, 2, 2, 1, 2, 2, 2, 2, 1, 2, 2, 2,
    2, 2, 2, 2, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 1, 2, 2, 2, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 2, 2, 2, 1,
    2, 2, 2, 2]]

@[expose] def hgens : List Table := hWords.map (wordTbl 275 abT)

@[expose] def fixV : List Nat := [99, 113, 144, 146, 175, 230, 239, 245, 260, 262, 264]

@[expose] def orbV : Array (List Nat) × Array Nat × Array Nat := hashSearch abArr fixV 779625

@[expose] def khGens : List Table := kgens ++ hgens

@[expose] def khWordA : List Nat := [3, 3, 5, 3, 5, 3, 3]

@[expose] def khWordB : List Nat :=
  [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2,
    2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2,
    2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1, 5, 5, 5, 5, 5, 5, 5,
    3, 3, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2,
    2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 5, 4, 3, 2,
    4, 4, 5, 5, 5, 5, 5, 5, 5, 4, 5, 5, 5, 5, 5, 5, 5, 4, 4, 3, 3]

end CFSG.LocalAnalysis.WeakClosure81.SporMcL
