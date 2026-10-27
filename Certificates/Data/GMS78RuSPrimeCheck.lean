module

public import Certificates.Data.GMS78RuSModelCheck

public section

namespace CFSG.GMS78RuSP

open CFSG.GMS78Ru CFSG.GMS78RuSim CFSG.GMS78RuQ CFSG.GMS78RuS

abbrev Pt : Type := Nat × Fin 8 × Fin 8

@[expose] def pMul (p q : Pt) : Pt := sMulF true p q

@[expose] def sqPt (p : Pt) : Pt := pMul p p

@[expose] def allPt : List Pt :=
  (List.range 256).flatMap fun c => all8.flatMap fun t => all8.map fun d => (c, t, d)

@[expose] def onePt : Pt := (0, 0, 0)

@[expose] def fPt : Pt := (0, 1, 0)

@[expose] def xPts : List Pt :=
  ([0, 1, 2, 3] : List Nat).flatMap fun m => all8.map fun t => (cOf m, t, 0)

@[expose] def inJ (p : Pt) : Bool :=
  xPts.all fun x => pMul p x == pMul x p || pMul p x == pMul fPt (pMul x p)

@[expose] def inCX (p : Pt) : Bool := xPts.all fun x => pMul p x == pMul x p

@[expose] def jPts : List Pt := allPt.filter inJ

@[expose] def encPt (p : Pt) : Nat := 64 * p.1 + 8 * p.2.1.val + p.2.2.val

@[expose] def decPt (i : Nat) : Pt := (i / 64, fin8Of (i / 8), fin8Of i)

@[expose] def jArr : Array Bool := (Array.range 16384).map fun i => inJ (decPt i)

@[expose] def jMem (p : Pt) : Bool := jArr.getD (encPt p) false

@[expose] def cmt (q p : Pt) : Bool := pMul p q == pMul q p

@[expose] def evenD (d : Fin 8) : Bool := d == 0 || d == 1 || d == 4 || d == 5

@[expose] def aPt : Pt := (102, 0, 0)

@[expose] def cPt : Pt := (0, 4, 4)

@[expose] def cntC (q : Pt) : Nat := allPt.countP (cmt q)

@[expose] def checkA : Bool := inJ aPt && !inCX aPt && sqPt aPt == onePt

@[expose] def checkCa : Bool := cntC aPt == 1024

@[expose] def checkCx : Bool :=
  jPts.all fun x => inCX x || sqPt x != onePt || decide (jPts.countP (cmt x) ≤ 128)

@[expose] def checkF1 : Bool :=
  allPt.all fun y => !cmt aPt y || !jMem (sqPt y) || jMem y || evenD y.2.2 ||
    jPts.any fun j => cmt aPt j && sqPt (pMul y j) == onePt

@[expose] def checkF3 : Bool :=
  inJ cPt && !inCX cPt && (jPts.filter inCX).all fun k =>
    sqPt (pMul k cPt) != onePt || allPt.any fun u => cmt (pMul k cPt) u && jMem (sqPt u) &&
      !jMem u && !evenD u.2.2 &&
        jPts.all fun j => !cmt (pMul k cPt) j || sqPt (pMul u j) != onePt

@[expose] def checkJd : Bool :=
  ([0, 1, 4, 5] : List (Fin 8)).all fun d => jPts.any fun j => j.2.2 == d

end CFSG.GMS78RuSP
