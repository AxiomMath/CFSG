module

public import Certificates.Kernel.Census.Suz.Data
import all Certificates.Kernel.Census.Suz.Data
import all Certificates.Data.Kernel.Census.Packed
import all Certificates.Data.Kernel.Census.PackedConj
import all CFSG.Certificates.Kernel.Enum.Defs
import all Mathlib.Data.List.Sort
import all Init.Data.Nat.Fold
import all Init.Data.Range.Basic
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelCensus.Suz

open CFSG.KC.Census

set_option maxRecDepth 1000000

theorem kPc : ppcOK 1782 11 suzXs suzRs suzCjs suzBs = true := by quickRfl

theorem kU0 : usF 0 = true := by quickRfl
theorem kU1 : usF 1 = true := by quickRfl
theorem kU2 : usF 2 = true := by quickRfl
theorem kU3 : usF 3 = true := by quickRfl
theorem kU4 : usF 4 = true := by quickRfl
theorem kU5 : usF 5 = true := by quickRfl

theorem kW0 : pinvRest 1782 11 suzXs 0 suzIm suzWt0 = some (suzIm.drop 255) := by
  decide +kernel
theorem kW1 : pinvRest 1782 11 suzXs 4096 (suzIm.drop 255) suzWt1 = some (suzIm.drop 463) := by
  decide +kernel
theorem kW2 : pinvRest 1782 11 suzXs 8192 (suzIm.drop 463) suzWt2 = some (suzIm.drop 663) := by
  decide +kernel
theorem kW3 : pinvRest 1782 11 suzXs 12288 (suzIm.drop 663) suzWt3 = some (suzIm.drop 911) := by
  decide +kernel

end CertificateChecks.KernelCensus.Suz

end
