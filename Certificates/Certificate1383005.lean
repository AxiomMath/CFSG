module

public import CFSG.OddTranspositions.PartThree.Eleven.Plus.RealizeCheck
import Certificates.Kernel.PlusRealize.Checks
import CFSG.Certificates.Kernel.PlusRealizeSound

public section

namespace Certificates

open CertificateChecks.KernelPlusR

open CFSG.OddTranspositions.PartThree.PlusRealize in
theorem certificate1383005 : realizeCheck () = true :=
  CFSG.KC.PlusRealizeK.realizeCheck_of ch1383005_zT ch1383005_zF ch1383005_zR ch1383005_rows
    ch1383005_sT ch1383005_sF ch1383005_tT ch1383005_tF ch1383005_dT ch1383005_dF ch1383005_cT
    ch1383005_cF

end Certificates
