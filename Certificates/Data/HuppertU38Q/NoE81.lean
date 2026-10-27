module

public import Certificates.Data.HuppertU38Q.Check

public section

namespace U38Sylow

open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.Monster.B.Fischer CFSG.RankThree.Native

@[expose] def commAt (a b : Array ℕ) : Bool := eqA 513 (compA 513 a b) (compA 513 b a)

@[expose] def cenOf (pts : Array (Array ℕ)) (i : ℕ) : List ℕ :=
  (List.range pts.size).filter fun j => commAt pts[i]! pts[j]!

@[expose] def nonAbelianAt (pts : Array (Array ℕ)) (C : List ℕ) : Bool :=
  C.any fun j => C.any fun k => !(commAt pts[j]! pts[k]!)

@[expose] def noE81Pts (pts : Array (Array ℕ)) : Bool :=
  let cens : List (ℕ × List ℕ) :=
    ((List.range pts.size).filter fun i => cubeOne pts[i]!).map fun i => (i, cenOf pts i)
  (cens.filter fun p => 243 ≤ p.2.length).length ≤ 80 &&
    cens.all fun p => p.2.length != 81 || nonAbelianAt pts p.2

@[expose] def noE81Check (_ : Unit := ()) : Bool := noE81Pts (qCert ()).pts

@[expose] def u38NoE81Check (_ : Unit := ()) : Bool := u38SylowCheck () && noE81Check ()

end U38Sylow
