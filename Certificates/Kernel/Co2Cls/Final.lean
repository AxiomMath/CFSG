module

public import Certificates.Kernel.Co2Cls.Card
public import Certificates.Kernel.Co2Cls.WMem
public import Certificates.Kernel.Co2J.Facts

public section

namespace CertificateChecks.KernelSpor.Co2Cls.Final

open CFSG.KC.Co2InvS CFSG.KC.Co2Syl CFSG.KC.TabMatGrp CFSG.KC.Co2Cls
  CertificateChecks.KernelSpor.Co2Syl CertificateChecks.KernelSpor.Co2Cls CFSG.RankThree.Co2

theorem MatP_HT {k : ℕ} (hk : k < 5) : MatP 22 (HT k) = wordMat sylWords[k]! := by
  rw [Nat.eq_of_beq_eq_true (gensT k hk), MatP_wordK (Co2Cls.sylWords_lt k hk)]

theorem genMonN_HT : genMonN 5 HT = matGrp sylWords :=
  genMon_eq_matGrp
    (fun j hj => ⟨j, by rw [CertificateChecks.KernelSpor.Co2J.sylWords_size]; exact hj, MatP_HT hj⟩)
    fun k hk => by
      rw [CertificateChecks.KernelSpor.Co2J.sylWords_size] at hk
      exact ⟨k, hk, MatP_HT hk⟩

theorem class0 : Nat.card (Conj (RP 0)) = 1 ∧ Nat.card (Cent (RP 0)) = 743178240 := by
  rw [← natCard_genMonN]
  exact Co2Cls.class0

theorem class1 : Nat.card (Conj (RP 1)) = 270 ∧ Nat.card (Cent (RP 1)) = 2 ^ 17 * 21 :=
  Co2Cls.class1 natCard_genMonN wmem1

theorem class2 : Nat.card (Conj (RP 2)) = 1260 ∧ Nat.card (Cent (RP 2)) = 2 ^ 16 * 9 :=
  Co2Cls.class2 natCard_genMonN wmem2

theorem class3 : Nat.card (Conj (RP 3)) = 1260 ∧ Nat.card (Cent (RP 3)) = 2 ^ 16 * 9 :=
  Co2Cls.class3 natCard_genMonN wmem3

theorem class4 : Nat.card (Conj (RP 4)) = 22680 ∧ Nat.card (Cent (RP 4)) = 2 ^ 15 :=
  Co2Cls.class4 natCard_genMonN

theorem class5 : Nat.card (Conj (RP 5)) = 15120 ∧ Nat.card (Cent (RP 5)) = 2 ^ 14 * 3 :=
  Co2Cls.class5 natCard_genMonN wmem5

theorem class6 : Nat.card (Conj (RP 6)) = 15120 ∧ Nat.card (Cent (RP 6)) = 2 ^ 14 * 3 :=
  Co2Cls.class6 natCard_genMonN wmem6

theorem class7 : Nat.card (Conj (RP 7)) = 1008 ∧ Nat.card (Cent (RP 7)) = 2 ^ 14 * 45 :=
  Co2Cls.class7 natCard_genMonN wmem7

theorem class8 : Nat.card (Conj (RP 8)) = 1008 ∧ Nat.card (Cent (RP 8)) = 2 ^ 14 * 45 :=
  Co2Cls.class8 natCard_genMonN wmem8

theorem class9 : Nat.card (Conj (RP 9)) = 120960 ∧ Nat.card (Cent (RP 9)) = 2 ^ 11 * 3 :=
  Co2Cls.class9 natCard_genMonN
    (by rw [genMonN_HT]; exact CertificateChecks.KernelSpor.Co2J.tFacts.pow)
    (by rw [genMonN_HT]; exact CertificateChecks.KernelSpor.Co2J.tFacts.card) wmem9

end CertificateChecks.KernelSpor.Co2Cls.Final

end
