module

public import Certificates.Data.Kernel.A8Nbr476K
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelA8N476

open CFSG.KC.A8N476 Certificates.A8Nbr476

theorem ch476001_words : wordsB wordData = true := by quickRfl

theorem ch476001_cover : coverB (codesL wordData) (codesC excCases) = true := by quickRfl

theorem ch476001_mon : monB monData = true := by quickRfl

theorem ch476001_len : allCases.length = 516 := by decide +kernel

theorem ch476001_fst : monData.map Prod.fst = excCases := by decide +kernel

theorem ch476001_exc : ∀ c ∈ excCases, c ∈ allCases := by decide +kernel

theorem neg476001_word :
    (!wordB ((false, 0, 0, 1), [0, 1, 2, 5, 0, 2, 1, 2, 5, 0, 2, 1, 2, 5])) = true := by quickRfl

theorem neg476001_cover : (!coverB (codesL wordData.tail) (codesC excCases)) = true := by quickRfl

theorem neg476001_mon : (!monE ((true, 3, 3, 2),
    [[1, 0, 0, 0], [0, 1, 0, 0], [0, 0, 1, 0], [0, 0, 0, 1]],
    [[1, 0, 0, 0], [0, 1, 0, 0], [0, 0, 1, 0], [0, 0, 0, 1]])) = true := by quickRfl

end CertificateChecks.KernelA8N476

end
