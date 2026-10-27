module

public import Certificates.Data.Kernel.Cert690.SqA8
public import Certificates.Kernel.Cert690.GrpPData
public import Certificates.Kernel.Cert690.SqPassData

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelC690.SqPass

open CFSG.KC.C690 CertificateChecks.KernelC690.GrpP

set_option maxHeartbeats 0 in
theorem invOm : invOKL Om.length Om = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem bitsOm : invBitsL (Nat.lor M1 M2) Om 0 = true := by decide +kernel

theorem bitsTop : (Nat.lor M1 M2).testBit 20160 = false := by decide +kernel

theorem om012 : Om[0]? = some 34630287489 ∧ Om[1]? = some r1 ∧ Om[2]? = some r2 := by
  decide +kernel

theorem r12 : r1 = 34647329153 ∧ r2 = 35704297409 := by decide +kernel

theorem m1Bits : M1.testBit 1 = true ∧ M1.testBit 2 = false := by decide +kernel

end CertificateChecks.KernelC690.SqPass

end
