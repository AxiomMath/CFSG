module

public import Certificates.Data.U42F431Perm
public import Certificates.Data.U42F431Tab
public import Certificates.Data.U42F431TabInv
public import Certificates.Data.U42F431TabFlag
public import Certificates.Data.U42F431LitT
public import Certificates.Data.U42F431LitP
public import Certificates.Data.U42F431LitI

public section

namespace U42F431

@[expose] def sameSet (a b : List Nat) : Bool :=
  ((a.filter (· < 45)).all fun p => b.contains p) && ((b.filter (· < 45)).all fun p => a.contains p)

@[expose] def imgSet (g : PL) (l : List Nat) : List Nat := l.map fun p => g.getD p 0

@[expose] def tpL (i : Nat) : PL :=
  comp (comp (evalW (wpW.getD i [])) xL) (evalW (invW (wpW.getD i [])))

@[expose] def tpTab : List PL := tpLit

@[expose] def chkTau : Bool :=
  ((List.range 45).all fun j => applyW (wpW.getD j []) 0 == j) &&
  (tpTab.getD 0 [] == xL) &&
  ((List.range 45).all fun i => (List.range 3).all fun k =>
    comp (comp (genL k) (tpTab.getD i [])) (genL (invLet k)) ==
      tpTab.getD ((genL k).getD i 0) []) &&
  ((List.range 45).all fun i => (List.range 45).all fun j =>
    i == j || tpTab.getD i [] != tpTab.getD j [])

@[expose] def chkP : Bool :=
  (p1W.length == 3) &&
  (p1W.all fun kw => (lnTab.getD kw.1 []).contains 0 && applyW kw.2 0 == 0 &&
    sameSet (imgSet (evalW kw.2) L0) (lnTab.getD kw.1 [])) &&
  ((List.range 27).filter (fun k => (lnTab.getD k []).contains 0) == p1W.map Prod.fst) &&
  (p2W.length == 5) &&
  (p2W.all fun pw => L0.contains pw.1 && applyW pw.2 0 == pw.1 &&
    sameSet (imgSet (evalW pw.2) L0) L0) &&
  (p2W.map Prod.fst == L0)

@[expose] def chkLines : Bool :=
  (lnTab.length == 27) && (lnTab.getD 0 [] == L0) &&
  lnTab.all (fun l => l.length == 5 && l.all (· < 45)) &&
  (lnTab.all fun l => (List.range 2).all fun k =>
    lnTab.any fun l' => sameSet (imgSet (genL k) l) l') &&
  ((List.range 27).all fun k =>
    sameSet (imgSet (evalW (wlW.getD k [])) L0) (lnTab.getD k [])) &&
  ((List.range 27).all fun i => (List.range 27).all fun j =>
    i == j || !sameSet (lnTab.getD i []) (lnTab.getD j []))


@[expose] def gTL (k : Nat) : PL := if k < 5 then gTLit.getD k [] else evalW (TgW.getD k [])

@[expose] def c3L : PL := c3Lit

@[expose] def Tl : List PL := TlLit

@[expose] def t0L : PL := Tl.getD t0Idx []

@[expose] def fixPts (g : PL) : List Nat := (List.range 45).filter fun p => g.getD p 0 == p

@[expose] def chkT : Bool :=
  (Tl.length == 64) && (Tpar.length == 64) &&
  ((List.range 64).all fun i => i == 0 ||
    ((Tpar.getD i (0, 0)).1 < i && (Tpar.getD i (0, 0)).2 < 5 &&
      Tl.getD i [] == comp (Tl.getD (Tpar.getD i (0, 0)).1 []) (gTL (Tpar.getD i (0, 0)).2))) &&
  (Tl.getD 0 [] == idL) &&
  ((List.range 64).all fun i => (List.range 5).all fun k =>
    Tl.contains (comp (Tl.getD i []) (gTL k))) &&
  ((List.range 64).all fun i => (List.range 64).all fun j =>
    i == j || Tl.getD i [] != Tl.getD j []) &&
  ((List.range 5).all fun k => (gTL k).getD 0 0 == 0 && sameSet (imgSet (gTL k) L0) L0) &&
  (comp c3L (comp c3L c3L) == idL) && (c3L != idL) && (c3L.getD 0 0 == 0) &&
  sameSet (imgSet c3L L0) L0 &&
  ((List.range 5).all fun k => Tl.contains (comp (comp c3L (gTL k)) (comp c3L c3L))) &&
  ((List.range 64).all fun i =>
    !((List.range 5).all fun k =>
      comp (Tl.getD i []) (gTL k) == comp (gTL k) (Tl.getD i [])) ||
      (Tl.getD i [] == idL || Tl.getD i [] == xL)) &&
  Tl.contains xL && (comp t0L t0L == idL) && (t0L != idL) &&
  ((fixPts xL).length == 13) && (fixPts t0L == L0)

@[expose] def chkInv : Bool :=
  (invDat.length == 64) &&
  ((List.range 64).all fun i =>
    !(comp (Tl.getD i []) (Tl.getD i []) == idL && Tl.getD i [] != idL) ||
      (comp (comp (evalW (invDat.getD i (0, [])).2) (Tl.getD i []))
          (evalW (invW (invDat.getD i (0, [])).2)) ==
        (if (invDat.getD i (0, [])).1 == 0 then xL else t0L)))


@[expose] def DL (j : Nat) : PL := if j < 8 then DLit.getD j [] else evalW (DW.getD j [])

@[expose] def alphaL (j a : Nat) : PL :=
  if a < 5 then gTL a else if a == 5 then c3L else DL j

@[expose] def evalAl (j : Nat) (w : List Nat) : PL :=
  w.foldr (fun a acc => comp (alphaL j a) acc) idL

@[expose] def alphaY (a : Nat) : PL :=
  if a < 5 then gTL a else if a == 5 then c3L else if a == 6 then DL 1 else DL 2

@[expose] def inB (g : PL) : Bool := g.getD 0 0 == 0 && sameSet (imgSet g L0) L0

@[expose] def chkLat : Bool :=
  (DW.length == 8) && (DW.getD 0 [] == []) &&
  ((DL 1).getD 0 0 == 0 && !sameSet (imgSet (DL 1) L0) L0) &&
  (sameSet (imgSet (DL 2) L0) L0 && (DL 2).getD 0 0 != 0) &&
  ((List.range 5).all fun i =>
    let j := i + 3
    evalAl j (farW.getD j ([], [])).1 == DL 1 && evalAl j (farW.getD j ([], [])).2 == DL 2) &&
  (evalW [] == idL) &&
  (yW.foldr (fun a acc => comp (alphaY a) acc) idL == yL) &&
  (flagDat.length == 135) &&
  ((List.range 27).all fun k => (List.range 5).all fun r =>
    let p := (lnTab.getD k []).getD r 0
    let jw := flagDat.getD (5 * k + r) (0, [])
    let b := evalW jw.2
    let g := comp b (DL jw.1)
    jw.1 < 8 && inB b && g.getD 0 0 == p && sameSet (imgSet g L0) (lnTab.getD k []))

@[expose] def commTab : List (List Bool) :=
  (List.range 64).map fun i => (List.range 64).map fun j =>
    comp (Tl.getD i []) (Tl.getD j []) == comp (Tl.getD j []) (Tl.getD i [])

@[expose] def zclT : List Bool := (List.range 64).map fun i => tpTab.contains (Tl.getD i [])

@[expose] def fixIdx (p : Nat) : List Nat :=
  (List.range 64).filter fun i => (Tl.getD i []).getD p 0 == p

@[expose] def stabIdx (k : Nat) : List Nat :=
  (List.range 64).filter fun i =>
    sameSet (imgSet (Tl.getD i []) (lnTab.getD k [])) (lnTab.getD k [])

@[expose] def agH (p k : Nat) : List Nat :=
  (fixLit.getD p []).filter fun i => (stabLit.getD k []).contains i

@[expose] def agOK (p k : Nat) : Bool :=
  ((List.range 64).any fun i =>
    !(agH p k).contains i && (agH p k).all fun h => (commTab.getD i []).getD h false) ||
  (agH p k).all fun h => !(zclT.getD h false) || Tl.getD h [] == xL

@[expose] def chkAg : Bool :=
  (List.range 45).all fun p => p == 0 || (List.range 27).all fun k => k == 0 || agOK p k

@[expose] def chkMisc : Bool :=
  (comp (comp (comp (tpTab.getD 31 []) (tpTab.getD 5 [])) (tpTab.getD 36 [])) (tpTab.getD 44 []) ==
    yL) &&
  ((List.range 5).any fun k =>
    !Tl.contains (comp (comp (DL 1) (gTL k)) (evalW (invW (DW.getD 1 []))))) &&
  ((List.range 5).any fun k =>
    !Tl.contains (comp (comp (DL 2) (gTL k)) (evalW (invW (DW.getD 2 []))))) &&
  (L0.all fun p => Tl.contains (tpTab.getD p []))

@[expose] def chkLit : Bool :=
  (tpLit.length == 45) && ((List.range 45).all fun i => tpLit.getD i [] == tpL i) &&
  (gTLit.length == 5) && ((List.range 5).all fun k => gTLit.getD k [] == evalW (TgW.getD k [])) &&
  (c3Lit == evalW c3W) &&
  (DLit.length == 8) && ((List.range 8).all fun j => DLit.getD j [] == evalW (DW.getD j [])) &&
  (fixLit.length == 45) && ((List.range 45).all fun p => fixLit.getD p [] == fixIdx p) &&
  (stabLit.length == 27) && ((List.range 27).all fun k => stabLit.getD k [] == stabIdx k)

end U42F431
