module

public import Certificates.Kernel.Misc.Perm.C2Data
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.TextGz

public section

namespace CertificateChecks.KernelCo2Three

open CertificateChecks.KernelMisc.Co2K (decodeHex)

#kc_repo #kc_text QMtHex "Certificates/Kernel/Co2Three/data/QMtHex.txt" 92081
  15590853108909189819

@[expose] def QMtArr : Array (Array Nat) := decodeHex QMtHex (List.replicate 761 1) 121

#kc_repo #kc_text QItHex "Certificates/Kernel/Co2Three/data/QItHex.txt" 22158
  6097442270769729034

@[expose] def QItArr : Array (Array Nat) :=
  decodeHex QItHex (2187 :: List.replicate 7 729 ++ [96]) 3

end CertificateChecks.KernelCo2Three

end
