module

public import CFSG.Walter.J1Recog.Pres

public section

namespace CFSG.Walter.Ree.T2.BaseFin

open CFSG.Walter.J1Recog Word

@[expose] def wj : Word 4 := gen 0

@[expose] def wc : Word 4 := gen 1

@[expose] def wt : Word 4 := gen 2

@[expose] def ww : Word 4 := gen 3

@[expose] def relsB : List (Word 4) :=
  [pow wj 2, pow wc 7, pow wt 3, wj ++ wt ++ inv wj ++ inv wt,
    inv wt ++ wc ++ wt ++ pow (inv wc) 2, pow (wj ++ inv wc ++ wj ++ wc) 2,
    pow (wj ++ pow (inv wc) 3 ++ wj ++ pow wc 3) 2,
    wj ++ inv wc ++ wj ++ wc ++ pow (inv wc) 5 ++ wj ++ pow wc 5]

@[expose] def relsW : List (Word 4) :=
  [pow ww 2, ww ++ wt ++ inv ww ++ inv wt, pow (ww ++ wc) 2, pow (ww ++ wj) 3]

@[expose] def relsHat : List (Word 4) := relsB ++ relsW

abbrev PresHat := PresentedGroup (relSet relsHat)

end CFSG.Walter.Ree.T2.BaseFin
