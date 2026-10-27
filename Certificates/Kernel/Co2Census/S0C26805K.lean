module

public import Certificates.Kernel.Co2Census.S0CK

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelCo2Census

open CFSG.KC.Co2InvS CFSG.KC.Co2Census

theorem C26805_tree :
    ∀ i < 23040, treeK (rmStep C26805GRt) 3 23040 C26805Pt C26805Xt i = true := by
  kc_cover 1024

theorem C26805_clos :
    ∀ i < 23040, closK (rmStep C26805GRt) 3 23040 C26805Pt C26805Xt i = true := by
  kc_cover 1024

theorem C26805_root : ∀ i < 23040, Nat.beq (rtOf C26805Xt i) 0 = true := by
  kc_cover 2048

theorem C26805_misc : centMisc C26805Pt C26805Gt C26805GRt 3 26805 = true := by
  decide +kernel

end CertificateChecks.KernelCo2Census
