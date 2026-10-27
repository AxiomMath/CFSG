module

public import Certificates.Kernel.Co2Cls.Final
public import Certificates.Kernel.Co2Fuse.Counts
public import CFSG.RankThree.Co2.ClassFacts
import Mathlib.Tactic.IntervalCases

public section

namespace CertificateChecks.KernelSpor.Co2Cls.Facts8102

open CFSG.KC.Co2InvS CFSG.KC.Co2Syl CFSG.KC.TabMatGrp CFSG.KC.Co2Cls
  CertificateChecks.KernelSpor.Co2Syl CertificateChecks.KernelSpor.Co2Cls CFSG.RankThree.Co2

theorem reps_invol : ∀ i < 10, involK (RP i) = true := by decide +kernel

theorem of_class {i a b : ℕ} (h : Nat.card (Conj (RP i)) = a ∧ Nat.card (Cent (RP i)) = b)
    (ha : a = classSizes[i]!) (hb : b * a = 743178240) :
    Nat.card (Conj (RP i)) = classSizes[i]! ∧ Nat.card (Cent (RP i)) * classSizes[i]! = 743178240 := by
  rw [h.1, h.2, ← ha]
  exact ⟨rfl, hb⟩

theorem classes : ∀ i < 10,
    Nat.card (Conj (RP i)) = classSizes[i]! ∧ Nat.card (Cent (RP i)) * classSizes[i]! = 743178240 := by
  intro i hi
  interval_cases i
  · exact of_class Final.class0 (by decide) (by norm_num)
  · exact of_class Final.class1 (by decide) (by norm_num)
  · exact of_class Final.class2 (by decide) (by norm_num)
  · exact of_class Final.class3 (by decide) (by norm_num)
  · exact of_class Final.class4 (by decide) (by norm_num)
  · exact of_class Final.class5 (by decide) (by norm_num)
  · exact of_class Final.class6 (by decide) (by norm_num)
  · exact of_class Final.class7 (by decide) (by norm_num)
  · exact of_class Final.class8 (by decide) (by norm_num)
  · exact of_class Final.class9 (by decide) (by norm_num)

theorem card_crConj {i : ℕ} (hi : i < 10) :
    Nat.card {x : Matrix (Fin 22) (Fin 22) (ZMod 2) // CrConj (repMat i) x} =
      Nat.card (Conj (RP i)) := by
  simp only [CrConj, repMat_eq hi, CertificateChecks.KernelSpor.Co2TInv.Cm_eq]

theorem card_cent {i : ℕ} (hi : i < 10) :
    Nat.card {g : Matrix (Fin 22) (Fin 22) (ZMod 2) // g ∈ Cm ∧ g * repMat i = repMat i * g} =
      Nat.card (Cent (RP i)) := by
  simp only [repMat_eq hi, CertificateChecks.KernelSpor.Co2TInv.Cm_eq]

theorem classFacts : ClassFacts where
  mem _ hi := CertificateChecks.KernelSpor.Co2Fuse.rep_mem_Cm hi
  sq i hi := by
    rw [repMat_eq hi]
    exact ((involK_iff (RP_lt hi)).1 (reps_invol i hi)).1
  ne_one i hi := by
    rw [repMat_eq hi]
    exact ((involK_iff (RP_lt hi)).1 (reps_invol i hi)).2
  conj i hi := by rw [card_crConj hi]; exact (classes i hi).1
  cent i hi := by rw [card_cent hi]; exact (classes i hi).2

end CertificateChecks.KernelSpor.Co2Cls.Facts8102

end
