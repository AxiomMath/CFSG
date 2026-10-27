module

public import Certificates.Kernel.Co2Smith.WDefs

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo2Smith

open CFSG.KC.Co2InvS CFSG.KC.Co2Smith CFSG.Sporadic.Co2Smith.Native

theorem wJc_k : wJcK = true := by decide +kernel
theorem wTabs_k : wTabsK = true := by decide +kernel
theorem wE1_k : wE1K = true := by decide +kernel
theorem wD0_k : wD0K = true := by decide +kernel
theorem whOK_k : whOKK = true := by decide +kernel
theorem wb_k : wbK = true := by decide +kernel
theorem filter_k : filterK = true := by decide +kernel
theorem wr0_k : wr0K = true := by decide +kernel
theorem wInj_k : wInjK = true := by decide +kernel
theorem wRel_k : wRelK = true := by decide +kernel

end CertificateChecks.KernelCo2Smith
