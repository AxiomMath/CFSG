module

public import Certificates.Kernel.Misc.Perm.C2Data
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.TextGz

public section

namespace CertificateChecks.KernelCo2Three

open CertificateChecks.KernelMisc.Co2K (decodeHex)

#kc_repo #kc_text_gz HMtHex "Certificates/Kernel/Co2Three/data/HMtHex.txt.gz" 13915
  13240034232236564855

@[expose] def HMtArr : Array (Array Nat) := decodeHex HMtHex (List.replicate 115 1) 121

#kc_repo #kc_text_gz HItHex "Certificates/Kernel/Co2Three/data/HItHex.txt.gz" 1647
  7729672916902229398

@[expose] def HItArr : Array (Array Nat) :=
  decodeHex HItHex ([8] ++ List.replicate 8 36 ++ [40, 40, 40, 40, 81, 12]) 3

end CertificateChecks.KernelCo2Three

end
