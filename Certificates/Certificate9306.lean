module

public import CFSG.ClassicalInvolution.SmallCases.NobqLists
import Certificates.Kernel.SmallSpor.M23RGlue
public import CFSG.ClassicalInvolution.SmallCases.Sporadic.Cover
public import CFSG.Sporadic.Schreier.MathieuOddCoreM23

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Nobq in
open CFSG.Blueprint CFSG.Certificates CFSG.Sporadic.Mathieu CFSG.Sporadic.Schreier
  CFSG.Sporadic.Th CFSG.Sporadic.Schreier.Native CFSG.ClassicalInvolution in
theorem certificate9306 : cqCheck m23Rep1 (enumerationTab m23CentQ1) = true := KernelSmallSpor.M23R.check9306

end Certificates
