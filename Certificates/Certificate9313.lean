module

public import CFSG.ClassicalInvolution.SmallCases.Sporadic.M23Inputs
import Certificates.Kernel.SmallSpor.M23Glue
public import CFSG.ClassicalInvolution.SmallCases.Sporadic.Basic

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.ClassicalInvolution in
open CFSG.Blueprint CFSG.Certificates CFSG.Sporadic.Mathieu CFSG.Sporadic.Schreier
  CFSG.Sporadic.Th CFSG.Sporadic.Schreier.Native in
theorem certificate9313 : twoConstrainedCheck (enumerationTab m23CentQ1) (permClosureList m23UGens1 20) 4 = true := KernelSmallSpor.M23.check9313

end Certificates
