module

public import CFSG.RankThree.PartTwo.Census.Carrier.Sp6TwoData
public meta import CFSG.RankThree.PartTwo.Census.Carrier.Sp6TwoData
public meta import Mathlib
public import Mathlib

public section

namespace CFSG.RankThree.PartTwo.Census.Carrier.Sp6Two

open CFSG.Quasithin.G2U

@[expose] def j6C : List ℕ :=
  (List.range 36).map fun t => if (t / 6 + 3) % 6 = t % 6 then 1 else 0

@[expose] def pairCheck (cc : List ℕ × List ℕ) : Bool :=
  canon6 cc.1 && canon6 cc.2 && mul6 cc.1 cc.2 == one6 && mul6 cc.2 cc.1 == one6 &&
    mul6 (mul6 (tr6 cc.1) j6C) cc.1 == j6C

@[expose] def commutes6 (x y : List ℕ) : Bool :=
  mul6 x y == mul6 y x

@[expose] def pow512 (x : List ℕ) : List ℕ :=
  (List.range 9).foldl (fun y _ => mul6 y y) x

@[expose] def orbitT (t : List ℕ) : Array (List ℕ) :=
  orbitBuild6 t gpsH (orbitParents6 t gpsH 4000)

@[expose] def closureT (gens : List (List ℕ)) : Array (List ℕ) :=
  build one6 mul6 gens (bfsParents one6 mul6 gens 24000)

abbrev orbit0 : Array (List ℕ) := orbitT t0C

abbrev orbit1 : Array (List ℕ) := orbitT t1C

abbrev orbit2 : Array (List ℕ) := orbitT t2C

abbrev orbit3 : Array (List ℕ) := orbitT t3C

abbrev cent0 : Array (List ℕ) := closureT (cent0P.map Prod.fst)

abbrev cent1 : Array (List ℕ) := closureT (cent1P.map Prod.fst)

abbrev cent2 : Array (List ℕ) := closureT (cent2P.map Prod.fst)

abbrev cent3 : Array (List ℕ) := closureT (cent3P.map Prod.fst)

abbrev pT0 : Array (List ℕ) := closureT (p0P.map Prod.fst)

abbrev pT1 : Array (List ℕ) := closureT (p1P.map Prod.fst)

abbrev sylowT : Array (List ℕ) := closureT (sylowP.map Prod.fst)

@[expose] def pairsOK : Bool :=
  genP.all pairCheck && tP.all pairCheck && cent0P.all pairCheck && cent1P.all pairCheck &&
    cent2P.all pairCheck && cent3P.all pairCheck && p0P.all pairCheck && p1P.all pairCheck &&
    sylowP.all pairCheck

@[expose] def invsOK : Bool :=
  tP.all fun cc => mul6 cc.1 cc.1 == one6 && !(cc.1 == one6)

@[expose] def commOK : Bool :=
  (cent0P ++ p0P).all (fun cc => commutes6 cc.1 t0C) &&
    (cent1P ++ p1P).all (fun cc => commutes6 cc.1 t1C) &&
    cent2P.all (fun cc => commutes6 cc.1 t2C) && cent3P.all (fun cc => commutes6 cc.1 t3C)

@[expose] def orbitOK (es : Array (List ℕ)) (n : ℕ) : Bool :=
  es.size == n && distinctCheck es && allCheck canon6 es

@[expose] def orbitsOK : Bool :=
  orbitOK orbit0 63 && orbitOK orbit1 315 && orbitOK orbit2 945 && orbitOK orbit3 3780

@[expose] def closureOK (gens : List (List ℕ)) (es : Array (List ℕ)) (n : ℕ) : Bool :=
  es.size == n && closedCheck mul6 gens es && distinctCheck es && allCheck canon6 es

@[expose] def centsOK : Bool :=
  closureOK (cent0P.map Prod.fst) cent0 23040 && closureOK (cent1P.map Prod.fst) cent1 4608 &&
    closureOK (cent2P.map Prod.fst) cent2 1536 && closureOK (cent3P.map Prod.fst) cent3 384

@[expose] def psOK : Bool :=
  closureOK (p0P.map Prod.fst) pT0 9 && closureOK (p1P.map Prod.fst) pT1 9

@[expose] def invP (m0 m1 m2 m3 : Std.HashMap (List ℕ) ℕ) (u : List ℕ) : Bool :=
  !(mul6 u u == one6) || u == one6 || found orbit0 m0 u || found orbit1 m1 u ||
    found orbit2 m2 u || found orbit3 m3 u

@[expose] def sylowOK : Bool :=
  closureOK (sylowP.map Prod.fst) sylowT 512 &&
    allCheck (invP (indexMap orbit0) (indexMap orbit1) (indexMap orbit2) (indexMap orbit3))
      sylowT

@[expose] def centralP (t pa pb : List ℕ) (q : List ℕ) : Bool :=
  !(commutes6 q pa && commutes6 q pb && pow512 q == one6) || q == one6 || q == t

@[expose] def twoOK : Bool :=
  allCheck (centralP t0C p0aC p0bC) cent0 && allCheck (centralP t1C p1aC p1bC) cent1

@[expose] def certAll : Bool :=
  pairsOK && invsOK && commOK && orbitsOK && centsOK && psOK && sylowOK && twoOK

end CFSG.RankThree.PartTwo.Census.Carrier.Sp6Two
