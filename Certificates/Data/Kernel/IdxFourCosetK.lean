module

public import Certificates.Data.Kernel.IdxFourChainK

public section

namespace CFSG.KC.IF4M

open CFSG.KC.IF4C

@[expose] noncomputable def wordM (MT : Nat) (w : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) idP (fun e _ ih => mulP (look MT e) ih) w

@[expose] noncomputable def negRec (T O PS B : List Nat) (k c : Nat) :
    Nat → List Nat → Nat → List Nat → Bool
  | j, [], r, [] =>
    if j < k then
      !(ap12 (look (T.getD j 0) (fld (PS.getD j 0) (ap12 r (B.getD j 0)))) (B.getD j 0) ==
        ap12 r (B.getD j 0))
    else j == k && !(ap12 r c == c) && decide (c < 4096)
  | j, a :: as, r, r' :: rs =>
    decide (a < O.getD j 0) && ap12 r (B.getD j 0) == ap12 (look (T.getD j 0) a) (B.getD j 0) &&
      r == mulP (look (T.getD j 0) a) r' && negRec T O PS B k c (j + 1) as r' rs
  | _, _, _, _ => false

@[expose] noncomputable def m0OK (SP : Nat) (T O PS B : List Nat) (MT Q QI : Nat)
    (AW CJ CS NG : List (List Nat)) : Bool :=
  allBelow 4 (fun g => Nat.beq (mulP (look MT g) (look MT (g + 4))) idP) &&
  allBelow 4 (fun a => Nat.beq (mulP (look Q a) (look QI a)) idP) &&
  Nat.beq (look Q 0) idP && Nat.beq (look Q 1) (look MT 0) && Nat.beq (look Q 2) (look MT 2) &&
  Nat.beq (look Q 3) (mulP (look MT 0) (look MT 2)) &&
  Nat.beq (wordM MT (AW.getD 0 [])) (look SP 0) && (AW.getD 0 []).all (fun e => decide (e < 4)) &&
  Nat.beq (wordM MT (AW.getD 1 [])) (look SP 1) && (AW.getD 1 []).all (fun e => decide (e < 4)) &&
  Nat.beq (look MT 3) (look SP 2) &&
  allBelow 4 (fun g => allBelow 3 (fun e => pathOK O (CJ.getD (3 * g + e) []) &&
    Nat.beq (mulP (look MT g) (mulP (look SP e) (look MT (g + 4))))
      (pathP T (CJ.getD (3 * g + e) [])))) &&
  allBelow 4 (fun g => allBelow 4 (fun a =>
    decide ((CS.getD (4 * g + a) []).getD 0 0 < 4) && pathOK O (CS.getD (4 * g + a) []).tail &&
    Nat.beq (mulP (look MT g) (mulP (look Q a) (look QI ((CS.getD (4 * g + a) []).getD 0 0))))
      (pathP T (CS.getD (4 * g + a) []).tail))) &&
  allBelow 4 (fun a => allBelow 4 (fun b => a == b ||
    (Nat.beq (((NG.getD (4 * a + b) []).drop (2 + (NG.getD (4 * a + b) []).getD 0 0)).getD 0 0)
        (mulP (look Q a) (look QI b)) &&
      negRec T O PS B 5 ((NG.getD (4 * a + b) []).getD 1 0) 0
        (((NG.getD (4 * a + b) []).drop 2).take ((NG.getD (4 * a + b) []).getD 0 0))
        (((NG.getD (4 * a + b) []).drop (2 + (NG.getD (4 * a + b) []).getD 0 0)).getD 0 0)
        ((NG.getD (4 * a + b) []).drop (2 + (NG.getD (4 * a + b) []).getD 0 0)).tail)))

end CFSG.KC.IF4M

end
