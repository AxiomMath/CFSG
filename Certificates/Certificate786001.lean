module

public import Certificates.Data.GrSLitL34FactsCF23SuzCheck
public import CFSG.Sporadic.SuzOddCore.Perms
import Certificates.Kernel.Sporadic.OddCore.Suz786001Glue

public section

namespace Certificates

open CertificateChecks

open CFSG.Sporadic.SuzOddCore CFSG.Monster.B.Co2 CFSG.ComponentClassification.GSThmB.CF23L34 in
theorem certificate786001 : suzM ≤ Subgroup.closure {CFSG.Monster.B.Co2.permOfArr 1782 suzY1Arr, CFSG.Monster.B.Co2.permOfArr 1782 suzY2Arr,
    CFSG.Monster.B.Co2.permOfArr 1782 suzMArr * CFSG.Monster.B.Co2.permOfArr 1782 suzY1Arr * (CFSG.Monster.B.Co2.permOfArr 1782 suzMArr)⁻¹,
    CFSG.Monster.B.Co2.permOfArr 1782 suzMArr * CFSG.Monster.B.Co2.permOfArr 1782 suzY2Arr * (CFSG.Monster.B.Co2.permOfArr 1782 suzMArr)⁻¹} :=
  KernelSpor.Suz786001.le_closure

end Certificates
