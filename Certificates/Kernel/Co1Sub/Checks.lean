module

public import Certificates.Kernel.Co1Sub.Data
public import Certificates.Data.Kernel.Co1Sub.Defs
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

public section

namespace CFSG.KD.Co1Sub

open CFSG.KC.Co1Sub CFSG.KC.Co1F2 CFSG.KLie.CT

@[expose] def tI : List Nat := [271, 272, 273, 274, 275]

@[expose] def aI : List Nat := [271, 272, 273, 274, 275, 300]

@[expose] def bI : List Nat := [271, 272, 273, 274, 275, 257, 258]

@[expose] def hI : List Nat := [271, 272, 273, 274, 275, 300, 257, 258]

theorem ch120801_gen : invsK G Gi = true := by quickRfl

theorem ch120801_aux : slpK G Gi aW aM aMi = true := by quickRfl

theorem ch120801_chain : slpK (pickL aM tI) (pickL aMi tI) tW tM tMi = true := by quickRfl

theorem ch120801_fix : fixK tM x0 = true := by quickRfl

theorem ch120801_t0 : treeK (pickL aM tI) x0 16384 t0 = true := by quickRfl

theorem ch120801_t1 : treeK tM x1 128 t1 = true := by quickRfl

theorem ch120801_fT : flagK (pickL aM tI) P0 fTP fTPi fTR = true := by quickRfl

theorem ch120801_fA : flagK (pickL aM aI) P0 fAP fAPi fAR = true := by quickRfl

theorem ch120801_fB : flagK (pickL aM bI) P0 fBP fBPi fBR = true := by quickRfl

theorem ch120801_nF : andB (Nat.beq (lenL fTP) 1)
    (andB (Nat.beq (lenL fAP) 3) (Nat.beq (lenL fBP) 405)) = true := by quickRfl

theorem ch120801_gw : slpK (pickL aM hI) (pickL aMi hI) gW gM gMi = true := by quickRfl

theorem ch120801_gAB : andB (Nat.beq (lenL gM) 38) (andB
    (Nat.beq (getL 0 gM 36) (getL 0 G 0)) (Nat.beq (getL 0 gM 37) (getL 0 G 1))) = true := by
  quickRfl

end CFSG.KD.Co1Sub

end
