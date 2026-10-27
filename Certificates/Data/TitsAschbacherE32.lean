module

public import Certificates.Data.TitsAschbacherSecFour

public section

namespace Certificates.TitsAschbacherE32

open CFSG.Sporadic.Schreier.Tits CFSG.Monster.B.Co2.Native Certificates.TitsAschbacherParrott
  Certificates.TitsAschbacherSecFour

@[expose] def hArr (w : List ℕ) : Array ℕ := prodArr titsHArrs w

@[expose] def hLetters (w : List ℕ) : Bool := w.all fun l => decide (l < 3)

@[expose] def isInvol (a : Array ℕ) : Bool :=
  eqA 1755 (compA 1755 a a) (idA 1755) && !eqA 1755 a (idA 1755)

@[expose] def fIdx : List ℕ := [7, 9, 10, 11, 12]

@[expose] def fBits (m : ℕ) : List ℕ :=
  (List.range 5).filterMap fun k => if m.testBit k then some (fIdx.getD k 0) else none

@[expose] def u10Bits (m : ℕ) : List ℕ :=
  (List.range 3).filterMap fun k => if m.testBit k then some (10 + k) else none

@[expose] def eArrs (_ : Unit) : List (Array ℕ) := (List.range 32).map fun m => vProd (u8Bits m)

@[expose] def fArrs (_ : Unit) : List (Array ℕ) := (List.range 32).map fun m => vProd (fBits m)

@[expose] def u10Arrs (_ : Unit) : List (Array ℕ) := (List.range 8).map fun m => vProd (u10Bits m)

@[expose] def sInvs (_ : Unit) : List (Array ℕ) := survivors5 1755 titsSLevels isInvol

@[expose] def xkData : List (Bool × Bool × List ℕ) :=
  [(false, true, []), (false, true, [2, 0, 1]), (false, true, [0, 1]), (false, false, []),
   (true, false, [3]), (true, false, [2, 3]), (false, true, [0]), (false, true, [1])]

@[expose] def xkConj (e : Bool × Bool × List ℕ) : Array ℕ := if e.1 then nArr e.2.2 else hArr e.2.2

@[expose] def xkSet (E F : List (Array ℕ)) (e : Bool × Bool × List ℕ) : List (Array ℕ) :=
  let c := xkConj e
  let ci := invCand 1755 c
  (if e.2.1 then F else E).map fun x => compA 1755 (compA 1755 c x) ci

@[expose] def pivotOK (E S : List (Array ℕ)) (X : List (List (Array ℕ))) (a : Array ℕ) : Bool :=
  E.any (eqA 1755 a) ||
    let ja := inJ a
    let om := S.filter fun b => commA a b && (!ja || inJ b)
    X.any fun xs => om.all fun b => xs.any (eqA 1755 b)

@[expose] def e32Check (_ : Unit) : Bool :=
  let E := eArrs ()
  let F := fArrs ()
  let S := sInvs ()
  let X := xkData.map (xkSet E F)
  all5 1755 titsSLevels (fun y => !isInvol y || S.any (eqA 1755 y)) &&
    xkData.all (fun e => (if e.1 then nLetters e.2.2 else hLetters e.2.2) &&
      isInvA 1755 (xkConj e) (invCand 1755 (xkConj e))) &&
    S.all (pivotOK E S X)

@[expose] def eOrbData : List (ℕ × ℕ × List ℕ) :=
  [(1, 1, [2, 0, 1]), (2, 2, [1, 2, 0, 1]), (3, 2, [2, 2, 0]), (4, 2, []), (5, 2, [0, 2, 1]),
   (6, 2, [0, 1]), (7, 2, [2, 1]), (8, 1, []), (9, 2, [0, 1, 2]), (10, 2, [0, 2]), (11, 1, [1]),
   (12, 2, [2]), (13, 1, [2, 1]), (14, 2, [0, 0, 2]), (15, 1, [0, 1]), (16, 0, []),
   (17, 1, [2, 1, 0]), (18, 2, [2, 0, 1]), (19, 2, [2, 0, 1, 2]), (20, 2, [1, 1]), (21, 2, [1]),
   (22, 2, [1, 2, 1]), (23, 2, [0]), (24, 1, [0, 0, 1]), (25, 2, [2, 0]), (26, 2, [0, 1, 1, 2]),
   (27, 1, [0, 0]), (28, 2, [1, 1, 2]), (29, 1, [0]), (30, 2, [1, 2]), (31, 1, [1, 0])]

@[expose] def eGenData : List (ℕ × ℕ × ℕ) :=
  [(2, 13, 15), (3, 8, 11), (4, 11, 15), (5, 8, 13), (6, 11, 13), (7, 8, 15), (9, 1, 8),
   (10, 1, 11), (12, 1, 13), (14, 1, 15), (18, 13, 31), (19, 8, 27), (20, 11, 31), (21, 8, 29),
   (22, 11, 29), (23, 8, 31), (25, 1, 24), (26, 1, 27), (28, 1, 29), (30, 1, 31)]

@[expose] def fOrbData : List (ℕ × ℕ × List ℕ) :=
  [(1, 3, [3, 0]), (2, 3, []), (3, 3, [2, 0, 3]), (4, 2, []), (5, 3, [3, 2]), (6, 3, [0, 0, 0, 2]),
   (7, 3, [1, 2, 3]), (8, 1, [3]), (9, 3, [1, 3]), (10, 3, [0, 0]), (11, 3, [2, 3, 2]),
   (12, 2, [0]), (13, 3, [3]), (14, 3, [0, 2]), (15, 3, [2, 3, 0]), (16, 1, []),
   (17, 3, [0, 1, 3]), (18, 3, [2]), (19, 3, [2, 3]), (20, 2, [1]), (21, 3, [0, 3, 2]),
   (22, 3, [0, 0, 0]), (23, 3, [0, 2, 3]), (24, 1, [2, 3]), (25, 3, [0, 3, 0]),
   (26, 3, [0, 0, 2]), (27, 3, [0, 0, 2, 3]), (28, 2, [0, 1]), (29, 3, [0, 3]), (30, 3, [0]),
   (31, 3, [3, 2, 3])]

@[expose] def fCommData : List (ℕ × List ℕ × List ℕ) :=
  [(7, [2, 2], [0, 1, 2, 0, 0]), (9, [0], [1, 1, 0, 1, 1]), (10, [0], [0, 0, 2, 2, 2, 2]),
   (11, [2, 2], [0, 1, 1, 2, 0]), (12, [0, 1], [1, 2, 1, 1, 0, 2])]

@[expose] def n0Word : List ℕ := [0]

@[expose] def mGens : List (Array ℕ) := (List.range 4).map (fun i => titsNArrs[i]!) ++
  [CFSG.Quasithin.titsPiArr]

@[expose] def conjToA (g x y : Array ℕ) : Bool := eqA 1755 (compA 1755 g x) (compA 1755 y g)

@[expose] def eOrbOK (E : List (Array ℕ)) (e : ℕ × ℕ × List ℕ) : Bool :=
  hLetters e.2.2 &&
    (if e.2.1 = 0 then eqA 1755 (E.getD e.1 #[]) (vA 12)
    else if e.2.1 = 1 then conjToA (hArr e.2.2) (vA 11) (E.getD e.1 #[])
    else conjToA (hArr e.2.2) (vA 10) (E.getD e.1 #[]))

@[expose] def fOrbOK (F U : List (Array ℕ)) (e : ℕ × ℕ × List ℕ) : Bool :=
  nLetters e.2.2 &&
    (if e.2.1 = 1 then conjToA (nArr e.2.2) (vA 12) (F.getD e.1 #[])
    else if e.2.1 = 2 then conjToA (nArr e.2.2) (vA 10) (F.getD e.1 #[])
    else conjToA (nArr e.2.2) (vA 9) (F.getD e.1 #[])) &&
    (U.any (eqA 1755 (F.getD e.1 #[])) == decide (e.2.1 ≤ 2))

@[expose] def orbCheck (_ : Unit) : Bool :=
  let E := eArrs ()
  let F := fArrs ()
  let U := u10Arrs ()
  eOrbData.all (eOrbOK E) && fOrbData.all (fOrbOK F U) &&
    eGenData.all (fun e => eqA 1755 (E.getD e.1 #[])
      (compA 1755 (E.getD e.2.1 #[]) (E.getD e.2.2 #[]))) &&
    mGens.all (fun g => fIdx.all fun i => F.any fun f => conjToA g (vA i) f) &&
    mGens.all (fun g => [10, 11, 12].all fun i => U.any fun u => conjToA g (vA i) u) &&
    U.all (fun a => U.all fun b => U.any (eqA 1755 (compA 1755 a b))) &&
    (List.range 32).all (fun a => (List.range 32).all fun b =>
      a == b || !eqA 1755 (F.getD a #[]) (F.getD b #[])) &&
    nLetters n0Word && conjToA (nArr n0Word) titsTArr (vA 10) &&
    fCommData.all (fun e => hLetters e.2.1 && hLetters e.2.2 &&
      eqA 1755 (compA 1755 (hArr e.2.1) (hArr e.2.2))
        (compA 1755 (compA 1755 (vA e.1) (hArr e.2.2)) (hArr e.2.1)))

end Certificates.TitsAschbacherE32
