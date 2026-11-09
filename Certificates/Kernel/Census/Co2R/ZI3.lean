module

public import Certificates.Kernel.Census.Co2R.Sub
public import CFSG.Certificates.Kernel.Common.EachTrue
import all Certificates.Kernel.Census.Co2R.Data
import all Certificates.Data.Kernel.Census.PackedConj
import all Certificates.Data.Kernel.Census.Packed
import all CFSG.Certificates.Kernel.Enum.Defs
import all Init.Data.Range.Basic
import CFSG.Certificates.Kernel.Common.Harness

public section

#kc_each CertificateChecks.KernelCensus.Co2R.Z kq
  (fun k => CertificateChecks.KernelCensus.Co2R.invChunk 32 CertificateChecks.KernelCensus.Co2R.Z.r 4096 k) 48 64


namespace CertificateChecks.KernelCensus.Co2R.Z

open CFSG.KC.Census CertificateChecks.KernelCensus.Co2R

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

theorem all_range'_four {f : ℕ → Bool} {a : ℕ} (h0 : f a = true) (h1 : f (a + 1) = true)
    (h2 : f (a + 2) = true) (h3 : f (a + 3) = true) : (List.range' a 4).all f = true := by
  rw [List.all_eq_true]
  intro k hk
  obtain ⟨hk1, hk2⟩ := List.mem_range'_1.1 hk
  obtain rfl | rfl | rfl | rfl : k = a ∨ k = a + 1 ∨ k = a + 2 ∨ k = a + 3 := by omega
  exacts [h0, h1, h2, h3]

theorem kI12 : invChunk 32 r 16384 12 = true :=
  invChunk_four 12 (Nat.le_trans (by decide) Z.wtLen) kq48 kq49 kq50 kq51
theorem kI13 : invChunk 32 r 16384 13 = true :=
  invChunk_four 13 (Nat.le_trans (by decide) Z.wtLen) kq52 kq53 kq54 kq55
theorem kI14 : invChunk 32 r 16384 14 = true :=
  invChunk_four 14 (Nat.le_trans (by decide) Z.wtLen) kq56 kq57 kq58 kq59
theorem kI15 : invChunk 32 r 16384 15 = true :=
  invChunk_four 15 (Nat.le_trans (by decide) Z.wtLen) kq60 kq61 kq62 kq63

theorem kI3 : (List.range' 12 4).all (invChunk 32 r 16384) = true :=
  all_range'_four kI12 kI13 kI14 kI15

end CertificateChecks.KernelCensus.Co2R.Z

end
