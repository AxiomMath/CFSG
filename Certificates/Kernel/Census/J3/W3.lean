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

theorem kW180 : (List.range' 180 5).all wordF = true := by quickRfl
theorem kW185 : (List.range' 185 5).all wordF = true := by quickRfl
theorem kW190 : (List.range' 190 5).all wordF = true := by quickRfl
theorem kW195 : (List.range' 195 5).all wordF = true := by quickRfl
theorem kW200 : (List.range' 200 5).all wordF = true := by quickRfl
theorem kW205 : (List.range' 205 5).all wordF = true := by quickRfl
theorem kW210 : (List.range' 210 5).all wordF = true := by quickRfl
theorem kW215 : (List.range' 215 5).all wordF = true := by quickRfl
theorem kW220 : (List.range' 220 5).all wordF = true := by quickRfl
theorem kW225 : (List.range' 225 5).all wordF = true := by quickRfl
theorem kW230 : (List.range' 230 5).all wordF = true := by quickRfl
theorem kW235 : (List.range' 235 5).all wordF = true := by quickRfl

end CertificateChecks.KernelCensus.J3

end
