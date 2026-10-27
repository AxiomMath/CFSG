module

public import CFSG.LocalAnalysis.StandardType.GGTablePThreeE6TableTDefs
import Certificates.Kernel.E6TT.TableTGlue

public section

namespace Certificates

open CertificateChecks

theorem certificate707001 : CFSG.StandardType.TablePThreeKG.E6TableTStmt :=
  KernelE6TT.e6TableT_kernel

end Certificates
