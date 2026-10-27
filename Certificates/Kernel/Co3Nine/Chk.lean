module

public import Certificates.Kernel.Co3Nine.Data
public import Certificates.Data.Kernel.Co3Nine.Defs
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.Co3Nine

open CFSG.KS.Co3Nine CFSG.Sporadic.Schreier.Co3

theorem chk : co39K Co3M.S Co3M.SI Co3T.S co3IndexNineYList co3IndexNineXWord co3IndexNineYWord
    KS ES = true := by
  quickRfl

end CertificateChecks.KernelSpor.Co3Nine

end
