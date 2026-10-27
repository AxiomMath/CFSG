module

public import CFSG.Sporadic.J4.QT2ANative

public section

namespace CFSG.Sporadic.J4.QT2A

open CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT

@[expose] def qWordG (sub : List Nat) (t : Nat) : List Int :=
  (List.range 6).flatMap fun i => if t.testBit i then qGenW.getD (sub.getD i 0) [] else []

@[expose] def conjDistinct (w : Nat → List Int) (X : Array V2) : Bool :=
  let ps := (List.range 64).map fun t => wR (w t)
  let pis := (List.range 64).map fun t => wR (invW (w t))
  let l := (List.zip ps pis).map fun p => mulRows (mulRows p.1 X) p.2
  l.all wfR && allDistinct l

@[expose] def qSub5 : List Nat := [0, 3, 5, 9, 10, 11]

@[expose] def chkQconj5 : Bool := conjDistinct (qWordG qSub5) (y5R ())

@[expose] def chkQlet : Bool := qGenW.all fun w => w.all fun l => l != 0

end CFSG.Sporadic.J4.QT2A
