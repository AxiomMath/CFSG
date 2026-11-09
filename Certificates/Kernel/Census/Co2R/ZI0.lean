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
  (fun k => CertificateChecks.KernelCensus.Co2R.invChunk 32 CertificateChecks.KernelCensus.Co2R.Z.r 4096 k) 0 16


namespace CertificateChecks.KernelCensus.Co2R.Z

open CFSG.KC.Census CertificateChecks.KernelCensus.Co2R

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

theorem kI0 : (List.range' 0 4).all (invChunk 32 r 16384) = true :=
  all_range'_four'
    (invChunk_four 0 (Nat.le_trans (by decide) Z.wtLen) kq0 kq1 kq2 kq3)
    (invChunk_four 1 (Nat.le_trans (by decide) Z.wtLen) kq4 kq5 kq6 kq7)
    (invChunk_four 2 (Nat.le_trans (by decide) Z.wtLen) kq8 kq9 kq10 kq11)
    (invChunk_four 3 (Nat.le_trans (by decide) Z.wtLen) kq12 kq13 kq14 kq15)

end CertificateChecks.KernelCensus.Co2R.Z

end
