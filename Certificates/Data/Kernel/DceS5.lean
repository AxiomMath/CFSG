module

public import CFSG.Certificates.Kernel.Bounds.LyAlt.DceS5
public import Certificates.Data.Kernel.LceSTab

public section

namespace CFSG.Certificates.DS5

open CFSG.KC.LyA.DceS

@[expose] noncomputable def stabOne (FB : Nat → Nat) (sh wd NF MD : Nat)
    (s : Nat × ((Nat → Nat) × (Nat × (Nat × (List Nat × (Nat × (Nat × (List Nat × (Nat × Nat))))))))) :
    Bool :=
  Prod.rec (motive := fun _ => Bool) (fun D r => Prod.rec (motive := fun _ => Bool) (fun EB r =>
  Prod.rec (motive := fun _ => Bool) (fun SG r => Prod.rec (motive := fun _ => Bool) (fun mD r =>
  Prod.rec (motive := fun _ => Bool) (fun C1 r => Prod.rec (motive := fun _ => Bool) (fun X0 r =>
  Prod.rec (motive := fun _ => Bool) (fun X1 r => Prod.rec (motive := fun _ => Bool) (fun C2 r =>
  Prod.rec (motive := fun _ => Bool) (fun Y0 Y1 =>
    andB (Nat.beq mD (bits MD (Nat.mul (nat_lit 20) D) (nat_lit 20)))
    (andB (stabStart EB)
    (andB (Nat.beq X0 (nat_lit 2))
    (andB (Nat.beq (runStab FB EB sh wd NF D SG C1 X0) X1)
    (andB (Nat.beq X1 (Nat.succ mD))
    (andB (Nat.beq Y0 (nat_lit 1))
    (andB (Nat.beq (runSorted (mat EB) (nat_lit 19) mD C2 Y0) Y1)
      (Nat.beq (sortedCount Y1) mD)))))))) r) r) r) r) r) r) r) r) s

@[expose] noncomputable def stabAll (FB : Nat → Nat) (sh wd NF MD : Nat)
    (L : List (Nat × ((Nat → Nat) × (Nat × (Nat × (List Nat × (Nat × (Nat × (List Nat × (Nat × Nat)))))))))) :
    Bool :=
  List.rec (motive := fun _ => Bool) true (fun s _ ih => andB (stabOne FB sh wd NF MD s) ih) L

@[expose] noncomputable def stabHas (D : Nat)
    (L : List (Nat × ((Nat → Nat) × (Nat × (Nat × (List Nat × (Nat × (Nat × (List Nat × (Nat × Nat)))))))))) :
    Bool :=
  List.rec (motive := fun _ => Bool) false
    (fun s _ ih => orB (Prod.rec (motive := fun _ => Bool) (fun D' _ => Nat.beq D' D) s) ih) L

@[expose] noncomputable def stabCover (MD ND AL : Nat)
    (L : List (Nat × ((Nat → Nat) × (Nat × (Nat × (List Nat × (Nat × (Nat × (List Nat × (Nat × Nat)))))))))) :
    Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun D ih => andB
    (orB (Nat.beq D (nat_lit 0)) (orB (notB (aliveD AL D))
      (orB (Nat.beq (bits MD (Nat.mul (nat_lit 20) D) (nat_lit 20)) (nat_lit 1)) (stabHas D L)))) ih) ND

@[expose] noncomputable def dceOk (FB HB GB TB WD OB RR : Nat → Nat)
    (sh wd LT LI TL VL NL ND NO nH nT nW NR NF I0 W Wi USQ UH WH AL MD NORD SUM qO qT : Nat)
    (Cs : List Nat) (S0 S1 : Nat) (Hs : List Nat) (H0 H1 : Nat) (Gs : List Nat) (G0 G1 : Nat)
    (Os : List Nat) (O0 O1 : Nat) (TSs : List Nat) (T0 T1 : Nat) (Ts : List Nat) (P0 P1 : Nat)
    (Vs : List Nat) (V0 V1 : Nat)
    (stabs : List (Nat × ((Nat → Nat) × (Nat × (Nat × (List Nat × (Nat × (Nat × (List Nat × (Nat × Nat)))))))))) :
    Bool :=
  andB constsOK7
  (andB (lettersOK LT LI TL VL NL)
  (andB (relsOK RR LT TL VL NL NR)
  (andB (CFSG.Certificates.LCE.relsNorm RR NR)
  (andB (wordsOK WD RR LI NL NR WH nW)
  (andB (usqOK RR LT LI TL VL NL NR USQ W Wi UH)
  (andB (Nat.blt ND (nat_lit 255))
  (andB (Nat.blt I0 NO)
  (andB (Nat.beq (Nat.mul nT NO) NORD)
  (andB (sumOK AL MD ND NORD SUM)
  (andB (Nat.blt NF (nat_lit 4294967296))
  (andB (Nat.beq H0 (nat_lit 1))
  (andB (Nat.beq (runHdr HB LT TL VL NL Hs H0) H1)
  (andB (Nat.beq H1 (Nat.succ nH))
  (andB (Nat.beq G0 (nat_lit 1))
  (andB (Nat.beq (runGom HB GB OB I0 nH Gs G0) G1)
  (andB (Nat.beq G1 (Nat.succ NO))
  (andB (Nat.beq O0 (nat_lit 1))
  (andB (Nat.beq (runSorted (pt OB) qO NO Os O0) O1)
  (andB (Nat.beq (sortedCount O1) NO)
  (andB (Nat.beq T0 (nat_lit 1))
  (andB (Nat.beq (runSorted (tS TB) qT nT TSs T0) T1)
  (andB (Nat.beq (sortedCount T1) nT)
  (andB (Nat.beq P0 (nat_lit 1))
  (andB (Nat.beq (runT TB OB RR LT TL VL NL NR nT I0 Ts P0) P1)
  (andB (Nat.beq P1 (Nat.succ nT))
  (andB (Nat.beq S0 (mkS (nat_lit 0) (nat_lit 1)))
  (andB (Nat.beq (runFacts FB HB GB TB WD sh wd LT TL VL NL ND NO nH nT nW W Wi Cs S0) S1)
  (andB (Nat.blt (nat_lit 0) S1)
  (andB (Nat.beq (sI S1) NF)
  (andB (Nat.beq V0 (nat_lit 1))
  (andB (Nat.beq (runCover FB OB sh wd NF NO AL Vs V0) V1)
  (andB (Nat.beq V1 (Nat.add (nat_lit 1) (Nat.shiftLeft ND (nat_lit 20))))
  (andB (stabAll FB sh wd NF MD stabs)
    (stabCover MD ND AL stabs))))))))))))))))))))))))))))))))))

end CFSG.Certificates.DS5

end
