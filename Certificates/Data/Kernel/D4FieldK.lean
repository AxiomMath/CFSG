module

public import Certificates.Data.Kernel.Misc.ArrEnum

public section

namespace CFSG.KC.D4Field

open CFSG.KC.Enum (pg allN)
open CFSG.KS (mask)
open CFSG.KC.Misc.ArrEnum (permB)

@[expose] noncomputable def ap (P x : Nat) : Nat := pg (nat_lit 12) (mask (nat_lit 12)) P x

@[expose] noncomputable def eqPt (f g : Nat → Nat) : Bool :=
  allN (nat_lit 2457) fun x => Nat.beq (f x) (g x)

@[expose] noncomputable def fp (F c x : Nat) : Nat :=
  bif Nat.beq c (nat_lit 1) then ap F x else ap F (ap F x)

@[expose] noncomputable def zAt (T : Nat → Nat) (F i c x : Nat) : Nat := ap (T i) (fp F c x)

@[expose] noncomputable def fOK (sift : Nat → Bool) (T QG : Nat → Nat) (F G0 PHI : Nat)
    (NJ : List Nat) : Bool :=
  permB (nat_lit 2457) (nat_lit 12) F && eqPt (fun x => ap F (ap F (ap F x))) (fun x => x) &&
    permB (nat_lit 2457) (nat_lit 12) G0 &&
    eqPt (ap G0) (fun x => ap F (ap PHI (ap PHI x))) && sift G0 &&
    eqPt (ap (T 0)) (fun x => x) &&
    (List.range 4).all fun k => Nat.blt (NJ.getD k 0) 81 &&
      eqPt (fun x => ap F (ap (QG k) x)) (fun x => ap (T (NJ.getD k 0)) (ap F x))

@[expose] noncomputable def rep (r : Nat × Nat) (c : Nat) : Nat := bif Nat.beq c 1 then r.1 else r.2

@[expose] noncomputable def zOK (T : Nat → Nat) (F : Nat) (CD : List (List Nat))
    (CR : List (Nat × Nat)) (i c o : Nat) (L C : List Nat) (P : List (Nat × Nat)) : Bool :=
  bif Nat.beq o 0 then
    !eqPt (fun x => zAt T F i c (zAt T F i c (zAt T F i c x))) (fun x => x)
  else
    ((List.range 81).all fun j => Nat.beq j 0 || L.any (Nat.beq j) ||
      !eqPt (fun x => ap (T j) (zAt T F i c x)) (fun x => zAt T F i c (ap (T j) x)) ||
      !eqPt (fun x => ap (T j) (ap (T j) (ap (T j) x))) (fun x => x)) &&
    Nat.beq L.length C.length &&
    ((L.zip C).all fun wc => bif Nat.beq wc.2 99 then
        allN (nat_lit 2457) (fun x => !Nat.beq (ap (T wc.1) x) x)
      else Nat.blt wc.2 P.length && L.all fun x =>
        (CD.getD (P.getD wc.2 (0, 0)).1 []).any (Nat.beq x) ||
          !eqPt (fun y => ap (T x) (ap (T wc.1) y)) (fun y => ap (T wc.1) (ap (T x) y))) &&
    (P.all fun ma => Nat.blt ma.1 10 && (CD.getD ma.1 []).any (Nat.beq ma.2) &&
      eqPt (zAt T F i c) (fun x => ap (T ma.2) (zAt T F (rep (CR.getD ma.1 (0, 0)) c) c x)))

@[expose] noncomputable def cOK (T W : Nat → Nat) (F : Nat) (D : List Nat) (r : Nat × Nat)
    (N : List Nat) (WL : List (Nat × (List Nat × Nat))) : Bool :=
  Nat.beq D.length 9 && Nat.beq (D.getD 0 1) 0 && Nat.beq N.length 8 &&
    eqPt (fun x => zAt T F r.2 2 (zAt T F r.2 2 x)) (zAt T F r.1 1) &&
    ((List.range 8).all fun q => bif Nat.beq (N.getD q 0) 0 then
        allN (nat_lit 2457) (fun x => !Nat.beq (ap (T (D.getD (q + 1) 0)) x) x)
      else WL.any (fun e => Nat.beq e.1 (N.getD q 0 - 1)) &&
        !eqPt (fun x => ap (W (N.getD q 0 - 1)) (ap (T (D.getD (q + 1) 0)) x))
          (fun x => ap (T (D.getD (q + 1) 0)) (ap (W (N.getD q 0 - 1)) x)) &&
        !eqPt (fun x => ap (W (N.getD q 0 - 1)) (ap (T (D.getD (q + 1) 0)) x))
          (fun x => ap (T (D.getD (q + 1) 0)) (ap (T (D.getD (q + 1) 0))
            (ap (W (N.getD q 0 - 1)) x)))) &&
    (WL.all fun e => Nat.blt e.1 4 && Nat.beq e.2.1.length 8 &&
      ((List.range 8).all fun q => D.any (Nat.beq (e.2.1.getD q 0)) &&
        eqPt (fun x => ap (W e.1) (ap (T (D.getD (q + 1) 0)) x))
          (fun x => ap (T (e.2.1.getD q 0)) (ap (W e.1) x))) &&
      D.any (Nat.beq e.2.2) &&
      eqPt (fun x => ap (W e.1) (zAt T F r.1 1 x))
        (fun x => ap (T e.2.2) (zAt T F r.1 1 (ap (W e.1) x))))

@[expose] noncomputable def fieldK (sift : Nat → Bool) (T QG W : Nat → Nat) (F G0 PHI : Nat)
    (NJ ZO : List Nat) (ZL ZC : List (List Nat)) (ZP : List (List (Nat × Nat)))
    (CD : List (List Nat)) (CR : List (Nat × Nat)) (CN : List (List Nat))
    (CW : List (List (Nat × (List Nat × Nat)))) : Bool :=
  fOK sift T QG F G0 PHI NJ &&
    ((List.range 4).all fun k => permB (nat_lit 2457) (nat_lit 12) (W k) && sift (W k)) &&
    ((List.range 162).all fun p => zOK T F CD CR (p / 2) (p % 2 + 1) (ZO.getD p 0) (ZL.getD p [])
      (ZC.getD p []) (ZP.getD p [])) &&
    (List.range 10).all fun m => cOK T W F (CD.getD m []) (CR.getD m (0, 0)) (CN.getD m [])
      (CW.getD m [])

end CFSG.KC.D4Field

end
