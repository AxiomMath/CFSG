module

public import Certificates.Data.DcRows

public section

namespace CFSG.Quasithin.H13.LocDbl.DcNative

@[expose] def subOrd3 (B : List Nat) (Yt : Array (Array Nat)) : Bool :=
  Yt.all fun t => B.all fun b => img t (img t (img t b)) == b

@[expose] def subEnumOK (n : Nat) (B : List Nat) (N cap : Nat) (Yt : Array (Array Nat)) : Bool :=
  let e := bfsEnumL n B Yt cap
  enumOK N Yt e.1 e.2 && distinctNat (rowKeys n B Yt e.1 e.2 N) && closedOK n B Yt e.1 e.2 N &&
    decide (0 < N)

@[expose] def lettersInv (n : Nat) (letters : Array (Array Nat)) : Bool :=
  letters.all fun t => (List.range n).all fun q => img (invTab t) (img t q) == q

@[expose] def subNorm (n : Nat) (B : List Nat) (N cap : Nat) (letters Yt : Array (Array Nat)) : Bool :=
  let e := bfsEnumL n B Yt cap
  let rows := enumRowList B Yt e.1 e.2 N
  letters.all fun t =>
    let ti := invTab t
    Yt.all fun y => rows.contains (B.map fun b => img t (img y (img ti b)))

@[expose] def subInOver (Yt : Array (Array Nat)) (D : DcData) : Bool :=
  D.Vs.all fun W =>
    let rows := enumRowList D.B (D.VG W.1) W.2.1 W.2.2.1 W.2.2.2
    Yt.all fun y => rows.contains (D.B.map (img y))

end CFSG.Quasithin.H13.LocDbl.DcNative
