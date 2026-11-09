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

theorem kW240 : (List.range' 240 5).all wordF = true := by quickRfl
theorem kW245 : (List.range' 245 5).all wordF = true := by quickRfl
theorem kW250 : (List.range' 250 5).all wordF = true := by quickRfl
theorem kW255 : (List.range' 255 5).all wordF = true := by quickRfl
theorem kW260 : (List.range' 260 5).all wordF = true := by quickRfl
theorem kW265 : (List.range' 265 5).all wordF = true := by quickRfl
theorem kW270 : (List.range' 270 5).all wordF = true := by quickRfl
theorem kW275 : (List.range' 275 5).all wordF = true := by quickRfl
theorem kW280 : (List.range' 280 5).all wordF = true := by quickRfl
theorem kW285 : (List.range' 285 5).all wordF = true := by quickRfl
theorem kW290 : (List.range' 290 5).all wordF = true := by quickRfl
theorem kW295 : (List.range' 295 5).all wordF = true := by quickRfl

end CertificateChecks.KernelCensus.J3

end
