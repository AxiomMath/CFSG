module

public import Certificates.Kernel.Census.M2217.Data
import all Certificates.Kernel.Census.M2217.Data
import all Certificates.Data.Kernel.Census.Packed
import all CFSG.Certificates.Kernel.Enum.Defs
import all Mathlib.Data.List.Sort
import all Init.Data.Nat.Fold
import all Init.Data.Range.Basic
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelCensus.M2217

set_option maxRecDepth 1000000

theorem kW0 : (List.range' 0 120).all wordF = true := by quickRfl
theorem kW120 : (List.range' 120 120).all wordF = true := by quickRfl
theorem kW240 : (List.range' 240 120).all wordF = true := by quickRfl
theorem kW360 : (List.range' 360 120).all wordF = true := by quickRfl
theorem kW480 : (List.range' 480 120).all wordF = true := by quickRfl
theorem kW600 : (List.range' 600 120).all wordF = true := by quickRfl
theorem kW720 : (List.range' 720 120).all wordF = true := by quickRfl
theorem kW840 : (List.range' 840 120).all wordF = true := by quickRfl
theorem kW960 : (List.range' 960 120).all wordF = true := by quickRfl
theorem kW1080 : (List.range' 1080 120).all wordF = true := by quickRfl
theorem kWt : (List.range' 1200 39).all wordF = true := by quickRfl

end CertificateChecks.KernelCensus.M2217

end
