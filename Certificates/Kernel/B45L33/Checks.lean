module

public import Certificates.Data.Kernel.B45L33
public import Certificates.Kernel.B45L33.Data

public section

namespace CertificateChecks.KD.B45L33

open CFSG.KC.B45L33

theorem ch260383_inv : invOK I = true := by decide +kernel

theorem ch260383_sym : symOK S = true := by decide +kernel

theorem ch260383_pairs : pairsOK I Pr = true := by decide +kernel

theorem ch260383_c3 : c3OK Pr W3 = true := by decide +kernel

end CertificateChecks.KD.B45L33
