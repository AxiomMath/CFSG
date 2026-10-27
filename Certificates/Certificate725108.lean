module

public import Certificates.Data.L52Insp443
import Certificates.Kernel.L52Insp443.OGlue

public section

open CFSG.SectionRank.QTK.Insp443.L52

public section

namespace Certificates

open CertificateChecks

open CFSG.SectionRank.QTK.Insp443.L52 in
theorem certificate725108 : chkOrb52 () = true := KernelL52I.chkOrb52_true

end Certificates

end
