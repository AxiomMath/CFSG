module

public import CFSG.RankThree.Co2.CensusData

public section

namespace CertificateChecks.KernelSpor.Co2J

open CFSG.RankThree.Co2

theorem sylWords_lt : ∀ k < 5, ∀ l ∈ sylWords[k]!, l < 42 := by decide +kernel
theorem jWords_lt : ∀ i < 10, ∀ l ∈ jWords[i]!, l < 42 := by decide +kernel

theorem sylWords_size : sylWords.size = 5 := by decide +kernel
theorem jWords_size : jWords.size = 10 := by decide +kernel

end CertificateChecks.KernelSpor.Co2J

end
