module

public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec5QFC
import Certificates.Kernel.Sol5Q.Glue

public section

namespace Certificates

theorem certificate6133 : ∀ (n : ℕ) [NeZero n], 8 ≤ n → n ≤ 11 → CFSG.OddStandard.Solomon75.FCAll n :=
  fun n _ hn hn' => by
    interval_cases n
    · exact CFSG.KD.Sol5Q.fcAll8
    · exact CFSG.KD.Sol5Q.fcAll9
    · exact CFSG.KD.Sol5Q.fcAll10
    · exact CFSG.KD.Sol5Q.fcAll11

end Certificates
