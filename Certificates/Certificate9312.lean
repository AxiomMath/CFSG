module

public import CFSG.ClassicalInvolution.SmallCases.Sporadic.M22Inputs
import Certificates.Kernel.SmallSpor.M22Glue
public import CFSG.ClassicalInvolution.SmallCases.Sporadic.Basic

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.ClassicalInvolution in
open CFSG.Blueprint CFSG.Certificates CFSG.Sporadic.Mathieu CFSG.Sporadic.Schreier
  CFSG.Sporadic.Th CFSG.Sporadic.Schreier.Native in
theorem certificate9312 : twoConstrainedCheck (enumerationTab m22CentQ1) (permClosureList m22UGens1 20) 6 = true := KernelSmallSpor.M22.check9312

end Certificates
