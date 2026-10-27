module

public import Certificates.Data.Item434OmegaMinus
import Certificates.Kernel.O8Minus434.Glue

public section

namespace Certificates

open CertificateChecks

open CFSG.RankThree.PartTwo.Sec4.Item434OmegaMinus in
theorem certificate8096 : eltsCheck = true ∧ wreathCheck = true ∧ centCheck = true ∧ genChainCheck = true := KernelO8M434.cert8096

end Certificates
