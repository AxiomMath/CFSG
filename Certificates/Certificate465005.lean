module

public import CFSG.LocalAnalysis.StandardType.TitsThreeOvergroupData
import Certificates.Kernel.TitsOver.Three.Glue

public section

namespace Certificates

open CertificateChecks

theorem certificate465005 : CFSG.StandardType.TitsThree.titsThreeCheck () = true :=
  KernelTitsOver.Three.titsThree_check

end Certificates
