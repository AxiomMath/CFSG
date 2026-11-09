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

theorem kW60 : (List.range' 60 5).all wordF = true := by quickRfl
theorem kW65 : (List.range' 65 5).all wordF = true := by quickRfl
theorem kW70 : (List.range' 70 5).all wordF = true := by quickRfl
theorem kW75 : (List.range' 75 5).all wordF = true := by quickRfl
theorem kW80 : (List.range' 80 5).all wordF = true := by quickRfl
theorem kW85 : (List.range' 85 5).all wordF = true := by quickRfl
theorem kW90 : (List.range' 90 5).all wordF = true := by quickRfl
theorem kW95 : (List.range' 95 5).all wordF = true := by quickRfl
theorem kW100 : (List.range' 100 5).all wordF = true := by quickRfl
theorem kW105 : (List.range' 105 5).all wordF = true := by quickRfl
theorem kW110 : (List.range' 110 5).all wordF = true := by quickRfl
theorem kW115 : (List.range' 115 5).all wordF = true := by quickRfl

end CertificateChecks.KernelCensus.J3

end
