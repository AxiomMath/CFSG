module

public import Certificates.Data.U42F431Check
public import Certificates.Data.U42F45Data

public section

namespace U42F431

@[expose] def ptLines (p : Nat) : List Nat :=
  (List.range 27).filter fun k => (lnTab.getD k []).contains p

@[expose] def layOK (isPt : Bool) (lp ll : List Nat) : Bool :=
  (if isPt then lp.getD 0 0 == 0 else ll.getD 0 0 == 0) &&
  ((List.range 45).all fun p => lp.getD p 0 ≤ 4) &&
  ((List.range 27).all fun k => ll.getD k 0 ≤ 4) &&
  ((List.range 45).all fun p => (isPt && p == 0) ||
    (ptLines p).any fun k => ll.getD k 0 + 1 == lp.getD p 0) &&
  ((List.range 27).all fun k => (!isPt && k == 0) ||
    (lnTab.getD k []).any fun p => lp.getD p 0 + 1 == ll.getD k 0) &&
  ((List.range 27).all fun k => (lnTab.getD k []).all fun p =>
    ll.getD k 0 ≤ lp.getD p 0 + 1 && lp.getD p 0 ≤ ll.getD k 0 + 1) &&
  ((List.range 45).all fun p => (ptLines p).all fun k => (ptLines p).all fun k' =>
    !(1 ≤ lp.getD p 0 && lp.getD p 0 < 4 && ll.getD k 0 + 1 == lp.getD p 0 &&
      ll.getD k' 0 + 1 == lp.getD p 0) || k == k') &&
  ((List.range 27).all fun k => (lnTab.getD k []).all fun p => (lnTab.getD k []).all fun p' =>
    !(1 ≤ ll.getD k 0 && ll.getD k 0 < 4 && lp.getD p 0 + 1 == ll.getD k 0 &&
      lp.getD p' 0 + 1 == ll.getD k 0) || p == p')

@[expose] def chkCyc : Bool :=
  (cycP.length == 4) && (cycL.length == 4) &&
  ((List.range 4).all fun i =>
    (lnTab.getD (cycL.getD i 0) []).contains (cycP.getD i 0) &&
    (lnTab.getD (cycL.getD i 0) []).contains (cycP.getD ((i + 1) % 4) 0) &&
    cycP.getD i 0 != cycP.getD ((i + 1) % 4) 0 && cycL.getD i 0 != cycL.getD ((i + 1) % 4) 0 &&
    cycP.getD i 0 < 45 && cycL.getD i 0 < 27)

@[expose] def coreIdx (ws : List (List Nat)) : List Nat :=
  (List.range 64).filter fun i => ws.all fun w =>
    Tl.contains (comp (comp (evalW (invW w)) (Tl.getD i [])) (evalW w))

@[expose] def chkF45Lay : Bool :=
  layOK true layPt0 layLn0 && layOK false layPt1 layLn1 && chkCyc

@[expose] def pairs3 : List (Nat × Nat) := [(0, 1), (0, 2), (1, 0), (1, 2), (2, 0), (2, 1)]

@[expose] def chkF45Pt : Bool :=
  (p1W.map Prod.fst == [0, 1, 2]) && (core1 == coreIdx (p1W.map Prod.snd)) &&
  (b01 < 45) && (layPt0.getD b01 0 == 4) && ((List.range 27).all fun k => layLn0.getD k 0 != 4) &&
  ((List.range 45).all fun p => layPt0.getD p 0 != 4 ||
    (core1.contains (farW1.getD p 0) && (Tl.getD (farW1.getD p 0) []).getD b01 0 == p)) &&
  (core1.all fun i => i == 0 || (Tl.getD i []).getD b01 0 != b01) &&
  ((List.range 6).all fun t =>
    applyW (two1.getD t []) 0 == 0 &&
    sameSet (imgSet (evalW (two1.getD t [])) (lnTab.getD 0 []))
      (lnTab.getD ((p1W.map Prod.fst).getD (pairs3.getD t (0, 0)).1 0) []) &&
    sameSet (imgSet (evalW (two1.getD t [])) (lnTab.getD 1 []))
      (lnTab.getD ((p1W.map Prod.fst).getD (pairs3.getD t (0, 0)).2 0) []))

@[expose] def pairs5 : List (Nat × Nat) :=
  [(0, 1), (0, 2), (0, 3), (0, 4), (1, 0), (1, 2), (1, 3), (1, 4), (2, 0), (2, 1), (2, 3), (2, 4),
    (3, 0), (3, 1), (3, 2), (3, 4), (4, 0), (4, 1), (4, 2), (4, 3)]

@[expose] def chkF45Ln : Bool :=
  (core2 == coreIdx (p2W.map Prod.snd)) && (b02 < 27) && (layLn1.getD b02 0 == 4) &&
  ((List.range 45).all fun p => layPt1.getD p 0 != 4) &&
  ((List.range 27).all fun k => layLn1.getD k 0 != 4 ||
    (core2.contains (farW2.getD k 0) &&
      sameSet (imgSet (Tl.getD (farW2.getD k 0) []) (lnTab.getD b02 [])) (lnTab.getD k []))) &&
  (core2.all fun i => i == 0 ||
    !sameSet (imgSet (Tl.getD i []) (lnTab.getD b02 [])) (lnTab.getD b02 [])) &&
  ((List.range 20).all fun t =>
    sameSet (imgSet (evalW (two2.getD t [])) L0) L0 &&
    (evalW (two2.getD t [])).getD (L0.getD 0 0) 0 == L0.getD (pairs5.getD t (0, 0)).1 0 &&
    (evalW (two2.getD t [])).getD (L0.getD 1 0) 0 == L0.getD (pairs5.getD t (0, 0)).2 0)

end U42F431
