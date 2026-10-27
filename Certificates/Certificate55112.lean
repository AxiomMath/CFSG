module

public import Certificates.Data.ExitTwoM12
import Certificates.Kernel.SmallSpor.M12QGlue

public section

namespace Certificates

open CertificateChecks

open CFSG.ClassicalInvolution.Q3.TL4.ExitTwo.M12 in
theorem certificate55112 : chkMemC () = true ∧ chkClosed () = true ∧ chkRoots () = true ∧ chkNorm () = true ∧
    chkBeta () = true ∧ chkWit () = true ∧ chkMeet () = true := KernelSmallSpor.M12Q.check55112

end Certificates
