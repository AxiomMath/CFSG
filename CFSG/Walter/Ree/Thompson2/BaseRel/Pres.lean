module

public import CFSG.Walter.J1Recog.Pres

public section

namespace CFSG.Walter.Ree.T2.BaseRel

open CFSG.Walter.J1Recog Word

@[expose] def ofChunks : List ℕ → ℕ
  | [] => 0
  | a :: l => Nat.lor a (Nat.shiftLeft (ofChunks l) 208)

@[expose] def wj : Word 4 := gen 0

@[expose] def wk : Word 4 := gen 1

@[expose] def wt : Word 4 := gen 2

@[expose] def wy : Word 4 := gen 3

@[expose] def nRels : List (Word 4) :=
  [pow wj 2, pow wt 3, pow wy 9, comm wj wt, wj ++ wy ++ wj ++ wy, inv wt ++ wy ++ wt ++ pow wy 2]

@[expose] def kRels : List (Word 4) := [pow wk 2, comm wj wk]

@[expose] def relA : Word 4 :=
  wk ++ inv wt ++ pow wy 3 ++ wk ++ pow (inv wy) 3 ++ wt ++ wk ++ inv wj ++ pow (inv wy) 2

@[expose] def kt3 : Word 4 := pow (wk ++ wt) 3

@[expose] def rels3024 : List (Word 4) := nRels ++ kRels ++ [relA]

@[expose] def rels1512 : List (Word 4) := nRels ++ kRels ++ [relA, kt3]

abbrev Pres3024 := PresentedGroup (relSet rels3024)

abbrev Pres1512 := PresentedGroup (relSet rels1512)

end CFSG.Walter.Ree.T2.BaseRel
