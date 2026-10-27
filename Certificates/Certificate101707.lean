module

public import Certificates.Data.Co2RowChk
import Certificates.Kernel.Co2I301.RowProof

public section

namespace Certificates

open CertificateChecks

theorem certificate101707 : CFSG.LocalAnalysis.GLTheoremA.H301B.Co2RowNative.co2RowCheck () = true :=
  KernelCo2I301.row_check

end Certificates
