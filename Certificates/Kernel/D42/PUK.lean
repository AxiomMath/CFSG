module

public import Certificates.Kernel.D42.PUD
public import Certificates.Kernel.OmegaEight.Arr3009K
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.Each

public section

set_option maxRecDepth 400000
set_option Elab.async false

namespace CFSG.KD.D42

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.MulH
open CertificateChecks.KernelO8

@[expose] noncomputable def invSK (p r : Nat) : Bool :=
  bAnd(cn p, bAnd(cn r, invEqK 360 9 (mask 9) (360 * 9) p r))

@[expose] noncomputable def cgK (i l : Nat) : Nat :=
  wO ((CFSG.ClassicalInvolution.O8Data.centGens.getD i []).getD l [])

@[expose] noncomputable def SU (i l : Nat) : Nat :=
  nIf(Nat.blt l 4, cgK i (Nat.sub l 1), pinv (cgK i (Nat.sub l 4)))

@[expose] noncomputable def zK (j : Nat) : Nat := mainK (nIf(Nat.beq j 0, 0, 2))

@[expose] noncomputable def commK (g z : Nat) : Bool := Nat.beq (pc g z) (pc z g)

@[expose] noncomputable def genP (G GI GJ : Nat → Nat) (j : Nat) : Bool :=
  allN 2 (fun l => bAnd(Nat.beq (G l) (pidn 360 9), bAnd(Nat.beq (GI l)
    (wA ((CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.D42Data.pWords.getD j []).getD l [])),
    bAnd(invSK (GI l) (GJ l), commK (GI l) (zK j)))))

@[expose] noncomputable def genU (G GI GJ : Nat → Nat) (j i k : Nat) : Bool :=
  bAnd(allN 3 (fun l => invSK (cgK i l) (pinv (cgK i l))),
  allN k (fun r => bAnd(Nat.beq (G r) (pidn 360 9), bAnd(Nat.beq (GI r)
    (wfoldK 360 9 (mask 9) (SU i)
      ((CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.D42Data.uWords.getD j []).getD r [])
      (pidn 360 9)),
    bAnd(invSK (GI r) (GJ r), bAnd(commK (GI r) (zK j),
      siftK 360 9 (mask 9) (360 * 9) (pidn 360 9) OmP.LR OmP.TRI OmP.BP 7 0 (GI r)))))))

theorem baseP0 : bAnd(Nat.beq P0.k 2, bAnd(Nat.beq P0.cnt 81,
    bAnd(penumHdK (pidn 360 9) P0.cnt 81 P0.T P0.PL, bAnd(genP P0.G P0.GI P0I 0,
    bAnd(Nat.beq U0.k 8, bAnd(Nat.beq U0.cnt 512,
    bAnd(penumHdK (pidn 360 9) U0.cnt 512 U0.T U0.PL, genU U0.G U0.GI U0I 0 0 8))))))) = true := by
  decide +kernel

theorem baseP1 : bAnd(Nat.beq P1.k 2, bAnd(Nat.beq P1.cnt 9,
    bAnd(penumHdK (pidn 360 9) P1.cnt 9 P1.T P1.PL, bAnd(genP P1.G P1.GI P1I 1,
    bAnd(Nat.beq U1.k 6, bAnd(Nat.beq U1.cnt 512,
    bAnd(penumHdK (pidn 360 9) U1.cnt 512 U1.T U1.PL, genU U1.G U1.GI U1I 1 2 6))))))) = true := by
  decide +kernel

@[expose] noncomputable def peP0 (s : Nat) : Bool :=
  penumSlK 360 9 (mask 9) (360 * 9) true P0.G P0.GI 2 P0.cnt P0.T P0.PL P0.POS P0.SRT P0.SRI
    (Nat.mul 16 s) 16

@[expose] noncomputable def peP1 (s : Nat) : Bool :=
  penumSlK 360 9 (mask 9) (360 * 9) true P1.G P1.GI 2 P1.cnt P1.T P1.PL P1.POS P1.SRT P1.SRI
    (Nat.mul 16 s) 16

@[expose] noncomputable def peU0 (s : Nat) : Bool :=
  penumSlK 360 9 (mask 9) (360 * 9) true U0.G U0.GI 8 U0.cnt U0.T U0.PL U0.POS U0.SRT U0.SRI
    (Nat.mul 32 s) 32

@[expose] noncomputable def peU1 (s : Nat) : Bool :=
  penumSlK 360 9 (mask 9) (360 * 9) true U1.G U1.GI 6 U1.cnt U1.T U1.PL U1.POS U1.SRT U1.SRI
    (Nat.mul 32 s) 32

@[expose] noncomputable def hsP (s : Nat) : Bool :=
  bAnd(slK P0.cnt (hsortPtK 360 9 (mask 9) P0.cnt P0.T P0.HS P0.HSI) (Nat.mul 81 s) 81,
    slK P1.cnt (hsortPtK 360 9 (mask 9) P1.cnt P1.T P1.HS P1.HSI) (Nat.mul 81 s) 81)

@[expose] noncomputable def hsU (s : Nat) : Bool :=
  bAnd(slK U0.cnt (hsortPtK 360 9 (mask 9) U0.cnt U0.T U0.HS U0.HSI) (Nat.mul 128 s) 128,
    slK U1.cnt (hsortPtK 360 9 (mask 9) U1.cnt U1.T U1.HS U1.HSI) (Nat.mul 128 s) 128)

@[expose] noncomputable def clP (s : Nat) : Bool :=
  bAnd(slK (Nat.mul P0.cnt 4) (findPtK P0.cnt P0.T
      (prodQK 360 9 (mask 9) 4 P0.T (bothK 2 P0.GI P0I)) P0Cl) (Nat.mul 324 s) 324,
    slK (Nat.mul P1.cnt 4) (findPtK P1.cnt P1.T
      (prodQK 360 9 (mask 9) 4 P1.T (bothK 2 P1.GI P1I)) P1Cl) (Nat.mul 324 s) 324)

@[expose] noncomputable def clU0 (s : Nat) : Bool :=
  slK (Nat.mul U0.cnt 16) (findPtK U0.cnt U0.T
    (prodQK 360 9 (mask 9) 16 U0.T (bothK 8 U0.GI U0I)) U0Cl) (Nat.mul 256 s) 256

@[expose] noncomputable def clU1 (s : Nat) : Bool :=
  slK (Nat.mul U1.cnt 12) (findPtK U1.cnt U1.T
    (prodQK 360 9 (mask 9) 12 U1.T (bothK 6 U1.GI U1I)) U1Cl) (Nat.mul 256 s) 256

@[expose] noncomputable def nqU (s : Nat) : Bool :=
  bAnd(slK (Nat.mul U0.cnt 2) (findPtK U0.cnt U0.T (conjQK 360 9 (mask 9) 2 U0.T P0.GI P0I) U0N)
      (Nat.mul 128 s) 128,
    slK (Nat.mul U1.cnt 2) (findPtK U1.cnt U1.T (conjQK 360 9 (mask 9) 2 U1.T P1.GI P1I) U1N)
      (Nat.mul 128 s) 128)

@[expose] noncomputable def lane (row r : Nat) : Nat :=
  Nat.land (Nat.shiftRight row (Nat.mul 9 r)) 511

@[expose] noncomputable def cmK (u y yi : Nat) : Nat := pc (pc (pc u y) (pinv u)) yi

@[expose] noncomputable def rinvK (p r : Nat) : Bool := bAnd(cn r, Nat.beq (pc p r) (pidn 360 9))

@[expose] noncomputable def rowGo (cntU : Nat) (UT : Nat → Nat) (y yi row : Nat) : Bool :=
  bAnd(allN 9 (fun r => bAnd(Nat.blt (lane row r) cntU,
      rinvK (UT (lane row r)) (pinv (UT (lane row r))))),
    allN 8 (fun r => Nat.blt (cmK (UT (lane row r)) y yi) (cmK (UT (lane row (Nat.succ r))) y yi)))

@[expose] noncomputable def rowOK (cntU : Nat) (UT : Nat → Nat) (y row : Nat) : Bool :=
  bAnd(rinvK y (pinv y), rowGo cntU UT y (pinv y) row)

@[expose] noncomputable def cmP0 (s : Nat) : Bool :=
  slK P0.cnt (fun i => bIf(Nat.beq i 0, true, rowOK U0.cnt U0.T (P0.T i) (P0C i)))
    (Nat.mul 10 s) 10

@[expose] noncomputable def cmP1 (s : Nat) : Bool :=
  slK P1.cnt (fun i => bIf(Nat.beq i 0, true, rowOK U1.cnt U1.T (P1.T i) (P1C i)))
    (Nat.mul 10 s) 10

theorem cmRow_neg : rowOK U0.cnt U0.T (P0.T 1) 0 = false := by decide +kernel

theorem genP_neg : genP P0.G P0.GI P0I 1 = false := by decide +kernel

end CFSG.KD.D42

end

set_option maxRecDepth 400000
set_option Elab.async false

set_option profiler true
set_option profiler.threshold 2000

#kc_each CFSG.KD.D42.peP0 0 6
#kc_each CFSG.KD.D42.peP1 0 1
#kc_each CFSG.KD.D42.hsP 0 1
#kc_each CFSG.KD.D42.clP 0 1
#kc_each CFSG.KD.D42.nqU 0 8
#kc_each CFSG.KD.D42.cmP0 0 9
#kc_each CFSG.KD.D42.cmP1 0 1
