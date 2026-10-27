module

public import CFSG.Certificates.Kernel.Common.DceS
public import CFSG.Certificates.Kernel.Co1.Model

public section

namespace CFSG.Certificates.Co1D

open CFSG.KC CFSG.KC.Loop CFSG.KC.DceS

@[expose] noncomputable def wtDceOK (WT : Nat → Nat) (m P : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun k ih => andB
    (orB (Nat.beq (WT k) (nat_lit 0)) (andB (Nat.blt (Nat.mod k P) m) (Nat.beq (WT k) (WT (Nat.mod k P)))))
    ih) (nat_lit 256)

@[expose] noncomputable def tgOK (PBT OMT : Nat → Nat) (NB I0 TGs ngT : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun k ih => andB ih
    (andB (isPerm (gk TGs k)) (gOmOK NB (PBT I0) (gk TGs k) (OMT I0)))) ngT

@[expose] noncomputable def dceOk (blk LT HT PBT OMT GT WT RT NE SE STT OHT TTE : Nat → Nat)
    (NB NO I0 BB BASEM NL TL ND ALIVE INV INV8 NR IH NH NW HS nf nN ngN SUMIDX TGs ngT nT
      hL hH hO hR hD P : Nat)
    (Cs CCs : List Nat) (S0 S1 X0 X1 : Nat) : Bool :=
  andB (constOK OMT NB NO I0 BB BASEM NL TL ND ALIVE)
  (andB (invSelfOK INV INV8 NL)
  (andB (invRelOK RT NL NR IH)
  (andB (allBelow NL hL (letOK LT TL))
  (andB (allBelow NH hH (hdrOK HT LT NL))
  (andB (allBelow NO hO (omOK PBT OMT GT HT NB NH (PBT I0)))
  (andB (wordsOK WT RT LT INV INV8 NL TL NR NW HS)
  (andB (allBelow NR hR (relOK RT LT NL TL))
  (andB (wtDceOK WT NW P)
  (andB (Nat.ble NL (Nat.mul (nat_lit 64) hL))
  (andB (Nat.ble NH (Nat.mul (nat_lit 64) hH))
  (andB (Nat.ble NO (Nat.mul (nat_lit 64) hO))
  (andB (Nat.ble NR (Nat.mul (nat_lit 64) hR))
  (andB (Nat.ble ND (Nat.mul (nat_lit 64) hD))
  (andB (Nat.ble ND (nat_lit 16384))
  (andB (Nat.blt NH (nat_lit 65536))
  (andB (Nat.blt nf (nat_lit 4294967296))
  (andB (Nat.blt nN (nat_lit 16777215))
  (andB (Nat.beq S0 (mkS (nat_lit 0) (nat_lit 1)))
  (andB (Nat.beq (runFacts blk LT HT PBT WT NL TL NB BB NH ND NO Cs S0) S1)
  (andB (Nat.beq S1 (mkS nf ND))
  (andB (Nat.beq X0 (nat_lit 1))
  (andB (Nat.beq (runCover blk PBT OMT NB NO hO ALIVE nf CCs X0) X1)
  (andB (Nat.beq X1 (Nat.succ ND))
  (andB (Nat.beq ngN (Nat.sub NL (nat_lit 1)))
  (andB (Nat.beq (eCnt (enumRun NE (nGens LT NL TL) ngN nN (nat_lit 0) nN (nat_lit 1))) (Nat.succ nN))
  (andB (Nat.blt SUMIDX failV)
  (andB (Nat.beq (indexSum blk SE STT nf nN ND hD ALIVE) SUMIDX)
  (andB (Nat.ble ngT (nat_lit 7))
  (andB (tgOK PBT OMT NB I0 TGs ngT)
  (andB (Nat.beq (eCnt (enumRun TTE TGs ngT nT (nat_lit 0) nT (nat_lit 1))) (Nat.succ nT))
  (andB (Nat.beq (Nat.mul nT NO) nN)
    (allBelow NO hO (CFSG.KC.Co1M.omClosOK LT PBT OMT OHT NL TL NB NO)))))))))))))))))))))))))))))))))

end CFSG.Certificates.Co1D

end
