module

public import Certificates.Data.U62Rank.Data
public import Certificates.Data.CFSGNative.Fi22.Local
public import CFSG.RankThree.Native.PermEnumeration
public import CFSG.Monster.B.Fischer.ArrCert

public section

namespace U62Rank

open CFSG.Monster.B.Co2.Native CFSG.Monster.B.Fischer CFSG.RankThree.Native CFSG.Perm.Native
  CFSG.Sporadic.Fi22.Native

@[expose] def parseNats (s : String) : Array ℕ :=
  (s.splitOn " ").toArray.filterMap fun t => t.toNat?

@[expose] def sylowGens (_ : Unit := ()) : Array (Array ℕ) :=
  ((sylowText ()).splitOn "|").toArray.map parseNats

@[expose] def keyPts (_ : Unit := ()) : List ℕ := t46Base.toList

@[expose] def qCert (_ : Unit := ()) : ArrCert := enumBfs 693 (sylowGens ()) (keyPts ()) 800

@[expose] def siftOK (_ : Unit := ()) : Bool :=
  allLt 3 fun k => sift (t46Trees ()) (t46Letters ()) t46Base (t46Q ()) 0 ((sylowGens ())[k]!)

@[expose] def expArr (c : ArrCert) (v : Array ℕ) : Array ℕ :=
  (List.range c.pts.size).foldl (fun e i =>
    if i == 0 then e else e.set! i ((e[c.par[i]!]! + v[c.lab[i]!]!) % 3))
    (Array.replicate c.pts.size 0)

@[expose] def expOK (c : ArrCert) (v e : Array ℕ) : Bool :=
  (e[0]! == 0) && allLt c.pts.size fun i =>
    i == 0 || (e[i]! == (e[c.par[i]!]! + v[c.lab[i]!]!) % 3)

@[expose] def cubeOne (a : Array ℕ) : Bool := eqA 693 (compA 693 a (compA 693 a a)) (idA 693)

@[expose] def commutes (a b : Array ℕ) : Bool := eqA 693 (compA 693 a b) (compA 693 b a)

@[expose] def witnessAt (c : ArrCert) (e : Array ℕ) : Bool :=
  (List.range c.pts.size).any (fun i => e[i]! == 0 && !cubeOne c.pts[i]!) ||
    (List.range c.pts.size).any (fun i => e[i]! == 0 &&
      (List.range c.pts.size).any (fun j => e[j]! == 0 && !commutes c.pts[i]! c.pts[j]!))

@[expose] def triples (_ : Unit := ()) : List (Array ℕ) :=
  (List.range 27).map fun k => #[k / 9 % 3, k / 3 % 3, k % 3]

@[expose] def finiteOK (c : ArrCert) : Bool :=
  (triples ()).all fun v =>
    let e := expArr c v
    expOK c v e && witnessAt c e

@[expose] def gensShapeOK (_ : Unit := ()) : Bool :=
  (sylowGens ()).size == 3 && allLt 3 fun k => (sylowGens ())[k]!.size == 693

@[expose] def u62RankCheck (_ : Unit := ()) : Bool :=
  let c := qCert ()
  gensShapeOK () && enumOK 693 (sylowGens ()) (keyPts ()) c && c.pts.size == 729 && siftOK () && finiteOK c

end U62Rank
