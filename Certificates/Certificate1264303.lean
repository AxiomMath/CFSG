module

public import CFSG.LocalAnalysis.UniquenessCase.UCFront10SporCo3CheckInputs
import Certificates.Kernel.Co3K.Glue

public section

open CFSG.LocalAnalysis.UniquenessCase.UC22.F10.Co3K

namespace CertificateChecks.Batch1264303

open CFSG.LocalAnalysis.UniquenessCase.UC22.F10.Co3K

private theorem co3K_check : co3KCheck = true := CertificateChecks.KernelCo3K.check

end CertificateChecks.Batch1264303

namespace Certificates

open CertificateChecks

open CFSG.LocalAnalysis.UniquenessCase.UC22.F10.Co3K in
theorem certificate1264303 : co3KCheck = true := CertificateChecks.Batch1264303.co3K_check

end Certificates
