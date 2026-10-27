module

public import Certificates.Data.Kernel.Antiflag.Kit
public import Certificates.Kernel.Antiflag.Data

public section

namespace CertificateChecks.KernelAntiflag

open CFSG.KD.Antiflag

theorem ch7135_g4 : chkG 4 (W 0) = true := by decide +kernel
theorem ch7135_s4 : chkS 4 (W 1) = true := by decide +kernel
theorem ch7135_t40 : chkT 4 (W 0) 0 (W 2) = true := by decide +kernel
theorem ch7135_t41 : chkT 4 (W 0) 1 (W 3) = true := by decide +kernel
theorem ch7135_t42 : chkT 4 (W 0) 2 (W 4) = true := by decide +kernel
theorem ch7135_t43 : chkT 4 (W 0) 3 (W 5) = true := by decide +kernel

theorem ch7135_g5 : chkG 5 (W 6) = true := by decide +kernel
theorem ch7135_s5 : chkS 5 (W 7) = true := by decide +kernel
theorem ch7135_t50 : chkT 5 (W 6) 0 (W 8) = true := by decide +kernel
theorem ch7135_t51 : chkT 5 (W 6) 1 (W 9) = true := by decide +kernel
theorem ch7135_t52 : chkT 5 (W 6) 2 (W 10) = true := by decide +kernel
theorem ch7135_t53 : chkT 5 (W 6) 3 (W 11) = true := by decide +kernel

end CertificateChecks.KernelAntiflag
