module

public import Certificates.Data.Kernel.Cert690.SqA8

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelC690.SqPass

open CFSG.KC.C690

theorem invPos : invOKL 2 [34630287489, 34630287426] = true := by decide +kernel

theorem invNeg : invOKL 2 [34630287489, 0] = false := by decide +kernel

theorem bitsPos : invBitsL 2 [34630287489, 34630287426] 0 = true := by decide +kernel

theorem bitsNegMissing : invBitsL 0 [34630287489, 34630287426] 0 = false := by decide +kernel

theorem bitsNegExtra : invBitsL 3 [34630287489, 34630287426] 0 = false := by decide +kernel

end CertificateChecks.KernelC690.SqPass

end
