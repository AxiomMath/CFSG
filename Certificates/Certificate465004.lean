module

public import CFSG.LocalAnalysis.StandardType.TitsFiveOvergroupData
import Certificates.Kernel.TitsOver.Five.Glue

public section

namespace Certificates

open CertificateChecks

theorem certificate465004 : CFSG.StandardType.TitsFive.titsFiveCheck () = true :=
  KernelTitsOver.Five.titsFive_check

end Certificates
