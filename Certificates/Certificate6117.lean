module

public import CFSG.Sporadic.Recognition.LyonsFinalLyInputs
public import CFSG.Sporadic.Recognition.LyonsFinalModularInputs
public import CFSG.Sporadic.Recognition.LyonsFinalCore107
import Certificates.Kernel.Ly6117.Facts

public section

namespace Certificates

open CFSG.Sporadic.Recognition.LyonsSims.LyFinal in
theorem certificate6117 : lyRelCheck (modularR Rcore107 modularD) = true :=
  CertificateChecks.KernelLy6117.lyRelCheck_true

end Certificates
