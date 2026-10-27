module

public import Certificates.Data.E3S3GenM12
import Certificates.Kernel.LocalComp.M12Cent.CoverFacts

public section

namespace Certificates

open CertificateChecks

open CFSG.ClassicalInvolution.Q3.TL4.E3S3M12 in
theorem certificate55119 : chkCover1 () = true ∧ chkGen1 () = true ∧ chkCover2 () = true ∧ chkGen2 () = true := KernelLC.M12Cent.coverFacts

end Certificates
