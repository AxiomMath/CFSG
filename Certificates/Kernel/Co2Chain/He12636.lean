
module

public import Certificates.Kernel.Co2Chain.He12636Cnt
public import Certificates.Kernel.Co2Chain.He12635
public import Certificates.Kernel.SporSch.HeT.CntGlue
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.ThetaSpor.HeThreeSmall
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.ThetaSpor.HeThreeInputs
public meta import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.ThetaSpor.HeThreeInputs
public meta import CFSG.Sporadic.HeldB.HeBlocks
public meta import Certificates.Data.CFSGNative.HeldB.Tests
public meta import Certificates.Data.CFSGNative.PairSchreier.Core
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo2Chain.He12636

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.SporSch CFSG.KC.BfsPin
open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.PairNative CFSG.Sporadic.HeldB
open CFSG.Sporadic.HeldB.Native CFSG.AGLEmbeddingD2.Wilson.ThetaSpor.He
open CertificateChecks.KernelSporSch CertificateChecks.KernelSpor
open CertificateChecks.KernelSporSch.HeO16 CertificateChecks.KernelSporSch.HeCn
open CertificateChecks.KernelCo2Chain

theorem kXA : permOK 8330 14 (mask 14) (8330 * 14) XA XAI = true := by quickRfl
theorem kXB : permOK 8330 14 (mask 14) (8330 * 14) XB XBI = true := by quickRfl
theorem kXA01 : bAnd(Nat.beq (pmR H36RXA 0) 0, Nat.beq (pmR H36RXA 1) 2) = true := by quickRfl
theorem kXB01 : bAnd(Nat.beq (pmR H36RXB 0) 0, Nat.beq (pmR H36RXB 1) 2) = true := by quickRfl
theorem kRXA : rbAll H36RXA XA = true := by quickRfl
theorem kRXB : rbAll H36RXB XB = true := by quickRfl
theorem kRYA : rbAll H36RYA (He12635.HT 0) = true := by quickRfl
theorem kRYB : rbAll H36RYB (He12635.HT 4) = true := by quickRfl
theorem kFA : nfValidK 5 HeC.LR FA = true := by quickRfl
theorem kFB : nfValidK 5 HeC.LR FB = true := by quickRfl
theorem kVA : Nat.beq (sumN 8330 VA) 7560 = true := by quickRfl
theorem kVB : Nat.beq (sumN 8330 VB) 504 = true := by quickRfl

theorem word0_eq {W : List (List Int)} {o cnt m : Nat} {Δ : Array Nat}
    (hk : He12635.classK W o cnt Δ m = true) :
    heThreeArr (W.getD 0 []) = unpack 8330 14 (He12635.HT o) := by
  unfold He12635.classK at hk
  rw [bAnd_iff] at hk
  have h := CFSG.KS.allN_spec hk.1 0 (by decide)
  rw [bAnd_iff] at h
  exact (wordEqK_sound He12635.hS CertificateChecks.KernelLC.HeFix.kPL2 h.1).1

theorem repYA : RepF 8330 (pmR H36RYA) (bOf heThreeWordsA) := by
  have h := rep_bOf bigDataA
  rw [word0_eq He12635.kA] at h
  exact repF_of_rb kRYA (repF_of_rep h)

theorem repYB : RepF 8330 (pmR H36RYB) (bOf heThreeWordsB) := by
  have h := rep_bOf bigDataB
  rw [word0_eq He12635.kB] at h
  exact repF_of_rb kRYB (repF_of_rep h)

theorem cardA : Nat.card {x : heP // bOf heThreeWordsA * (x : Equiv.Perm (Fin 8330)) =
    x * bOf heThreeWordsA} = 7560 := by
  have hX := repF_of_rb kRXA (rep_pm kXA)
  have hc : ∀ s < 49, cjB H36RXA H36RYA FA s = true := c12636CA.all
  have h01 := (bAnd_iff (Nat.beq (pmR H36RXA 0) 0) (Nat.beq (pmR H36RXA 1) 2)).1 kXA01
  rw [cent_of_or hX repYA kFA hc (Nat.eq_of_beq_eq_true h01.1) (Nat.eq_of_beq_eq_true h01.2)
    (hxy_of_mem hX repYA kFA hc bOf_mem) (e := 8330) (fun h => absurd h (by norm_num)) c12636OA.all]
  exact Nat.eq_of_beq_eq_true kVA

theorem cardB : Nat.card {x : heP // bOf heThreeWordsB * (x : Equiv.Perm (Fin 8330)) =
    x * bOf heThreeWordsB} = 504 := by
  have hX := repF_of_rb kRXB (rep_pm kXB)
  have hc : ∀ s < 49, cjB H36RXB H36RYB FB s = true := c12636CB.all
  have h01 := (bAnd_iff (Nat.beq (pmR H36RXB 0) 0) (Nat.beq (pmR H36RXB 1) 2)).1 kXB01
  rw [cent_of_or hX repYB kFB hc (Nat.eq_of_beq_eq_true h01.1) (Nat.eq_of_beq_eq_true h01.2)
    (hxy_of_mem hX repYB kFB hc bOf_mem) (e := 8330) (fun h => absurd h (by norm_num)) c12636OB.all]
  exact Nat.eq_of_beq_eq_true kVB

end CertificateChecks.KernelCo2Chain.He12636

end
