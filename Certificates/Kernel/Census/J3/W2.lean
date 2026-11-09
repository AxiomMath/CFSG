module

public import Certificates.Kernel.Census.J3.Words
import all Certificates.Kernel.Census.J3.Data
import all Certificates.Kernel.Census.J3.Words
import all Certificates.Data.Kernel.Census.Packed
import all CFSG.Certificates.Kernel.Enum.Defs
import all Init.Data.Nat.Fold
import all Init.Data.Range.Basic
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelCensus.J3

set_option maxRecDepth 1000000

theorem kW120 : (List.range' 120 5).all wordF = true := by quickRfl
theorem kW125 : (List.range' 125 5).all wordF = true := by quickRfl
theorem kW130 : (List.range' 130 5).all wordF = true := by quickRfl
theorem kW135 : (List.range' 135 5).all wordF = true := by quickRfl
theorem kW140 : (List.range' 140 5).all wordF = true := by quickRfl
theorem kW145 : (List.range' 145 5).all wordF = true := by quickRfl
theorem kW150 : (List.range' 150 5).all wordF = true := by quickRfl
theorem kW155 : (List.range' 155 5).all wordF = true := by quickRfl
theorem kW160 : (List.range' 160 5).all wordF = true := by quickRfl
theorem kW165 : (List.range' 165 5).all wordF = true := by quickRfl
theorem kW170 : (List.range' 170 5).all wordF = true := by quickRfl
theorem kW175 : (List.range' 175 5).all wordF = true := by quickRfl

end CertificateChecks.KernelCensus.J3

end
