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
  (fun k => CertificateChecks.KernelCensus.Co2R.invChunk 32 CertificateChecks.KernelCensus.Co2R.Z.r 4096 k) 16 32


namespace CertificateChecks.KernelCensus.Co2R.Z

open CFSG.KC.Census CertificateChecks.KernelCensus.Co2R

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

theorem kI1 : (List.range' 4 4).all (invChunk 32 r 16384) = true :=
  all_range'_four'
    (invChunk_four 4 (Nat.le_trans (by decide) Z.wtLen) kq16 kq17 kq18 kq19)
    (invChunk_four 5 (Nat.le_trans (by decide) Z.wtLen) kq20 kq21 kq22 kq23)
    (invChunk_four 6 (Nat.le_trans (by decide) Z.wtLen) kq24 kq25 kq26 kq27)
    (invChunk_four 7 (Nat.le_trans (by decide) Z.wtLen) kq28 kq29 kq30 kq31)

end CertificateChecks.KernelCensus.Co2R.Z

end
