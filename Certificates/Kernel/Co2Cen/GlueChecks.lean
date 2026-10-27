module

public import Certificates.Kernel.Co2Cen.GlueData
public import Certificates.Kernel.Co2Cen.Data
public import Certificates.Kernel.Co2J.Data
public import Certificates.Kernel.Co2Syl.Small
public import Certificates.Kernel.Co2Census.TInvCls
public import CFSG.RankThree.Co2.ZuWordsData
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.Cover
public import Certificates.Data.Kernel.Co2Census

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelSpor.Co2Cen

open CFSG.KC.Co2InvS CFSG.KC.Co2Syl CFSG.KC.Co2Cls CFSG.KC.Co2J CFSG.KC.Co2Cen
  CertificateChecks.KernelSpor.Co2Syl CertificateChecks.KernelSpor.Co2TInv CFSG.RankThree.Co2

@[expose] def zuClsT : List Nat := [0, 0, 7, 8, 8, 7, 1, 1, 3, 2, 5, 6, 6, 5, 3, 2]

theorem wGen : jGenK WGx = true := by quickRfl

theorem wInP1 : ∀ k < 5, CFSG.KC.Co2J.wordK G1 (WW1 k) (WL1 k) (Co2JRank.WG k) = true := by
  kc_cover 5

theorem lookW : ∀ s < 15,
    andK (lookC CFS NCS (bitMul Co2JRank.WG 5 (lwU s)) (lwA s) 133)
      (lookC CFS NCS (mulV (bitMul Co2JRank.WG 5 (lwU s)) (RP 1)) (lwB s) 42) = true := by
  kc_cover 15

theorem lwU_lt : ∀ s < 15, lwU s < 32 := by decide +kernel

theorem lwU_inj : ∀ s < 15, ∀ t < 15, lwU s = lwU t → s = t := by decide +kernel

theorem lwU_cover : ∀ u < 32, u = 0 ∨ u = 1 ∨ ∃ s < 15, lwU s = u ∨ lwU s = u ^^^ 1 := by
  decide +kernel

theorem lookZ : ∀ m < 15, lookC CFS NCS (AE (m + 1)) (LZ m) 1023 = true := by kc_cover 15

theorem lookZ_cls : ∀ m < 15, Nat.land (LZ m) 15 = zuClsT.getD (m + 1) 0 := by decide +kernel

theorem F8_eq : ∀ i < 16, F8 i = i := by decide +kernel

theorem gaZu : ∀ i < 4, Nat.beq (GA i) (CertificateChecks.KernelSpor.Co2Syl.wordK zuGenWords[i]!) =
    true := by kc_cover 4

theorem fix1_JE : ∀ i < 4,
    Nat.beq (Co2J.JE (F1 i)) (lAt [IDP, RP 1, RP 0, mulV (RP 0) (RP 1)] i) = true := by kc_cover 4

theorem repRk : ∀ j < 6, rankL (Nat.xor (RP (lAt [0, 1, 2, 3, 5, 7] j)) IDP) (elemOf (RK j))
    (scQ (RK j)) (lAt [6, 8, 6, 8, 8, 6] j) = true := by kc_cover 6

theorem odd3 : andK (Nat.beq (powK (CertificateChecks.KernelSpor.Co2Syl.wordK x3W) 3) IDP)
    (andK (commK (CertificateChecks.KernelSpor.Co2Syl.wordK x3W) (RP 1))
      (notK (commK (Co2JRank.WG 2) (CertificateChecks.KernelSpor.Co2Syl.wordK x3W)))) = true := by
  quickRfl

theorem odd7 : andK (Nat.beq (powK (CertificateChecks.KernelSpor.Co2Syl.wordK x7W) 7) IDP)
    (andK (commK (CertificateChecks.KernelSpor.Co2Syl.wordK x7W) (RP 1))
      (notK (commK (Co2JRank.WG 2) (CertificateChecks.KernelSpor.Co2Syl.wordK x7W)))) = true := by
  quickRfl

theorem xW_lt : (∀ l ∈ x3W, l < 42) ∧ ∀ l ∈ x7W, l < 42 := by decide

end CertificateChecks.KernelSpor.Co2Cen

end
