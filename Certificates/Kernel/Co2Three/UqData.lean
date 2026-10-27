module

public import Certificates.Kernel.Misc.Perm.C2Data
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.TextGz

public section

namespace CertificateChecks.KernelCo2Three

open CertificateChecks.KernelMisc.Co2K (decodeHex)

#kc_repo #kc_text_gz UqHex "Certificates/Kernel/Co2Three/data/UqHex.txt.gz" 5815
  13833161396273815605

@[expose] def UqArr : Array (Array Nat) := decodeHex UqHex [480, 729, 729] 3

end CertificateChecks.KernelCo2Three

end
