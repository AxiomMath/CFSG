module

public import Certificates.Kernel.AE6Core.Chain
public import Certificates.Kernel.AE6F.Checks
public import Certificates.Data.Kernel.AE6Core
public import Certificates.Data.Kernel.AE6Sm
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelAE6Sm

open CFSG.KC.Enum CFSG.KC.YoshQ CFSG.KC.AE6F CFSG.KC.AE6Core CFSG.KC.AE6Sm
  Certificates.AE6Model
open CertificateChecks.KernelAE6F (RG)
open CertificateChecks.KernelAE6Core

theorem ch517503c1 : commAllN RG zWord [[0], [1], [2], [4], [5], [6], [7]] = true := by
  decide +kernel

theorem ch517503c2 : commAllN RG zWord (cutWord :: conjWords) = true := by decide +kernel

theorem ch517503k : k0N RG kWords = true := by decide +kernel

theorem ch517503t : twinsN RG PL.S = true := by decide +kernel

end CertificateChecks.KernelAE6Sm

end
