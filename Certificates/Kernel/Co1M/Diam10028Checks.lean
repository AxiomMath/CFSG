module

public import Certificates.Kernel.Co1M.Diam10028
public meta import Certificates.Kernel.LocalComp.BlockGen

public section

set_option maxRecDepth 400000

#lc_blocks CertificateChecks.KernelCo1M.Diam.Blk CertificateChecks.KernelCo1M.Diam.diamAt 98280 256

namespace CertificateChecks.KernelCo1M.Diam

theorem diam_all : ∀ p < 98280, diamAt p = true :=
  CFSG.KC.Co3Bfs.cover_of_blocks (nb := 384) (by decide) (by decide) Blk.all

end CertificateChecks.KernelCo1M.Diam

end
