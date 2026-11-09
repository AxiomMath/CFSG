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
  (fun k => CertificateChecks.KernelCensus.Co2R.invChunk 32 CertificateChecks.KernelCensus.Co2R.Z.r 4096 k) 32 48


namespace CertificateChecks.KernelCensus.Co2R.Z

open CFSG.KC.Census CertificateChecks.KernelCensus.Co2R

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

theorem kI2 : (List.range' 8 4).all (invChunk 32 r 16384) = true :=
  all_range'_four'
    (invChunk_four 8 (Nat.le_trans (by decide) Z.wtLen) kq32 kq33 kq34 kq35)
    (invChunk_four 9 (Nat.le_trans (by decide) Z.wtLen) kq36 kq37 kq38 kq39)
    (invChunk_four 10 (Nat.le_trans (by decide) Z.wtLen) kq40 kq41 kq42 kq43)
    (invChunk_four 11 (Nat.le_trans (by decide) Z.wtLen) kq44 kq45 kq46 kq47)

end CertificateChecks.KernelCensus.Co2R.Z

end
