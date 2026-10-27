module

public import Certificates.Data.D4HexF48Check
import Certificates.Kernel.S63K.F4236

public section

namespace Certificates

open CertificateChecks

theorem certificate4236 : CFSG.D4Hex.hexF48Check CFSG.D4Hex.f48Order CFSG.D4Hex.f48Base CFSG.D4Hex.f48NWord
      CFSG.D4Hex.f48QWord CFSG.D4Hex.f48FWords CFSG.D4Hex.f48BWords CFSG.D4Hex.lineTab
      CFSG.D4Hex.lay0 CFSG.D4Hex.permArrs = true ∧
    CFSG.D4Hex.hexF48Check CFSG.D4Hex.f48Order3 CFSG.D4Hex.f48Base CFSG.D4Hex.f48NWord
      CFSG.D4Hex.f48QWord CFSG.D4Hex.f48FWords CFSG.D4Hex.f48BWords CFSG.D4Hex.lineTab
      CFSG.D4Hex.lay0 CFSG.D4Hex.permArrs = true := KernelS63.F4236.c4236

end Certificates
