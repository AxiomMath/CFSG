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

theorem kW0 : (List.range' 0 5).all wordF = true := by quickRfl
theorem kW5 : (List.range' 5 5).all wordF = true := by quickRfl
theorem kW10 : (List.range' 10 5).all wordF = true := by quickRfl
theorem kW15 : (List.range' 15 5).all wordF = true := by quickRfl
theorem kW20 : (List.range' 20 5).all wordF = true := by quickRfl
theorem kW25 : (List.range' 25 5).all wordF = true := by quickRfl
theorem kW30 : (List.range' 30 5).all wordF = true := by quickRfl
theorem kW35 : (List.range' 35 5).all wordF = true := by quickRfl
theorem kW40 : (List.range' 40 5).all wordF = true := by quickRfl
theorem kW45 : (List.range' 45 5).all wordF = true := by quickRfl
theorem kW50 : (List.range' 50 5).all wordF = true := by quickRfl
theorem kW55 : (List.range' 55 5).all wordF = true := by quickRfl

end CertificateChecks.KernelCensus.J3

end
