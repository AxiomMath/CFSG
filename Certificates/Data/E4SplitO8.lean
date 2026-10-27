module

public import Certificates.Data.E4QuatO8Check
public import Certificates.Data.E4SplitCheck

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.E4O8

open CFSG.EvenSmallLie.OmegaEight CFSG.Monster.B.Co2.Native CFSG.ClassicalInvolution.Q3.TL4.E4A

@[expose] def splitWords : List (List ℤ) := [[2, -3, -1, 2, -3, -1], [1, 2, -1, 3, 2, -3]]

@[expose] def splitW (_ : Unit) : List (List ℤ) := splitWords.map (cw 0)

@[expose] def splitA (_ : Unit) : List (Array ℕ) := (splitW ()).map omegaW

@[expose] def scheck (_ : Unit) : Bool :=
  wordsOK (splitW ()) && splitCheckA 360 (L0A ()) (xA 0) (u0A ()) (v0A ()) (wsA ()) (splitA ())

end CFSG.ClassicalInvolution.Q3.TL4.E4O8
