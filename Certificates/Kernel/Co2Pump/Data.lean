module

public import Certificates.Kernel.Misc.Perm.C2Data
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.TextGz

public section

namespace CertificateChecks.KernelCo2Pump

open CertificateChecks.KernelMisc.Co2K (decodeHex)

#kc_repo #kc_text_gz PMtHex "Certificates/Kernel/Co2Pump/data/PMtHex.txt.gz" 1936
  14171209981164008075

@[expose] def PMtArr : Array (Array Nat) := decodeHex PMtHex (List.replicate 16 1) 121

#kc_repo #kc_text_gz DMtHex "Certificates/Kernel/Co2Pump/data/DMtHex.txt.gz" 10648
  3092441231490317288

@[expose] def DMtArr : Array (Array Nat) := decodeHex DMtHex (List.replicate 88 1) 121

#kc_repo #kc_text_gz PAMtHex "Certificates/Kernel/Co2Pump/data/PAMtHex.txt.gz" 144353
  14468232923609409144

@[expose] def PAMtArr : Array (Array Nat) := decodeHex PAMtHex (List.replicate 1193 1) 121

#kc_repo #kc_text_gz PAItHex "Certificates/Kernel/Co2Pump/data/PAItHex.txt.gz" 20916
  7394038898670473403

@[expose] def PAItArr : Array (Array Nat) := decodeHex PAItHex [2200, 1193, 1193, 1193, 1193] 3

#kc_repo #kc_text_gz PBMtHex "Certificates/Kernel/Co2Pump/data/PBMtHex.txt.gz" 249502
  14829434826702795819

@[expose] def PBMtArr : Array (Array Nat) := decodeHex PBMtHex (List.replicate 2062 1) 121

#kc_repo #kc_text_gz PBItHex "Certificates/Kernel/Co2Pump/data/PBItHex.txt.gz" 31344
  15090290941883061118

@[expose] def PBItArr : Array (Array Nat) := decodeHex PBItHex [2200, 2062, 2062, 2062, 2062] 3

end CertificateChecks.KernelCo2Pump

end
