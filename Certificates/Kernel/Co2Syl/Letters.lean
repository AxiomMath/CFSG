module

public import Certificates.Kernel.Co2Syl.Small
public import CFSG.RankThree.Co2.ClassesCertInputs
public import CFSG.RankThree.Co2.XData

public section

namespace CertificateChecks.KernelSpor.Co2Syl

open CFSG.RankThree.Co2

theorem letters : ∀ l < 42, ∀ t < 22, (letterRows l)[t]! = lAt LT l / 2 ^ (22 * t) % 2 ^ 22 := by
  decide +kernel

theorem RW_eq : RW = repWords := by decide +kernel

theorem repWords_lt : ∀ j < 10, ∀ l ∈ repWords[j]!, l < 42 := by decide +kernel

theorem pWords1_lt : ∀ k < 5, ∀ l ∈ pWords1[k]!, l < 42 := by decide +kernel
theorem pWords3_lt : ∀ k < 5, ∀ l ∈ pWords3[k]!, l < 42 := by decide +kernel
theorem pWords4_lt : ∀ k < 4, ∀ l ∈ pWords4[k]!, l < 42 := by decide +kernel
theorem pWords5_lt : ∀ k < 5, ∀ l ∈ pWords5[k]!, l < 42 := by decide +kernel
theorem pWords6_lt : ∀ k < 5, ∀ l ∈ pWords6[k]!, l < 42 := by decide +kernel
theorem pWords8_lt : ∀ k < 5, ∀ l ∈ pWords8[k]!, l < 42 := by decide +kernel

theorem pWords1_size : pWords1.size = 5 := by decide +kernel
theorem pWords3_size : pWords3.size = 5 := by decide +kernel
theorem pWords4_size : pWords4.size = 4 := by decide +kernel
theorem pWords5_size : pWords5.size = 5 := by decide +kernel
theorem pWords6_size : pWords6.size = 5 := by decide +kernel
theorem pWords8_size : pWords8.size = 5 := by decide +kernel

end CertificateChecks.KernelSpor.Co2Syl

end
