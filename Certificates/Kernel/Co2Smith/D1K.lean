module

public import Certificates.Kernel.Co2Smith.D1Defs

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo2Smith

open CFSG.Sporadic.Co2Smith.Native

theorem d1Elt_k : d1EltK = true := by decide +kernel

theorem d1Lam1_k : d1Lam1K = true := by decide +kernel

theorem d1Lam2_k : d1Lam2K = true := by decide +kernel

theorem d1Dec_k : d1DecK = true := by decide +kernel

theorem d1Tree_k : d1TreeK = true := by decide +kernel

theorem d1OrbW_k : (d1Orb.toList.all fun p => p.all (· < 22)) = true := by decide +kernel

theorem d1Orb_k : d1OrbK = true := by decide +kernel

theorem d1Phi_k : d1PhiK = true := by decide +kernel

theorem d1Root_k : d1RootK = true := by decide +kernel

theorem d1Break_k : d1BreakK = true := by decide +kernel

theorem d1_neg : (!d1Nodup ((d1Orb.toList.take 2).map d1oK ++ [d1oK []]) &&
    !d1In d1X0K zK) = true := by
  decide +kernel

end CertificateChecks.KernelCo2Smith
