module

public import Certificates.Kernel.Census.Co2R.DataL
import all Certificates.Kernel.Census.Co2R.DataL
import all Certificates.Kernel.Census.Co2R.Data
import all Certificates.Data.Kernel.Census.PackedConjL
import all Certificates.Data.Kernel.Census.PackedL
import all Certificates.Data.Kernel.Census.PackedConj
import all Certificates.Data.Kernel.Census.Packed
import all CFSG.Certificates.Kernel.Enum.Defs
import all Init.Data.Range.Basic
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelCensus.Co2R.Z

open CFSG.KC.Census CertificateChecks.KernelCensus.Co2R

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

theorem kIH : invHead 32 r = true := by quickRfl

theorem kZl : Nat.ble (r.d.us.toList.zip r.d.roots).length (4 * 1536) = true := by quickRfl

theorem kFitC : fitW 160 r.d.cs.toList = true := by quickRfl

theorem kFitI : fitW 160 r.d.ci.toList = true := by quickRfl

theorem kRL0 : rootChunkL 32 160 r 1536 0 = true := by quickRfl
theorem kRL1 : rootChunkL 32 160 r 1536 1 = true := by quickRfl
theorem kRL2 : rootChunkL 32 160 r 1536 2 = true := by quickRfl
theorem kRL3 : rootChunkL 32 160 r 1536 3 = true := by quickRfl

end CertificateChecks.KernelCensus.Co2R.Z

end
