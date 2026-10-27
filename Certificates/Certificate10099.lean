module

public import CFSG.YGroups.Exact.Y332Inputs
public import CFSG.YGroups.Defs
import Certificates.Kernel.YModel.Y332Chain

public section

namespace Certificates

open CertificateChecks.KernelYModel

open CFSG.YGroups in
theorem certificate10099 :
    y332Arrays.size = 9 ∧
      ModelNative.permsOK 28162 y332Arrays = true ∧
      ModelNative.relatorsOK 28162 y332Arrays (yRels 3 3 2) = true ∧
      ModelNative.chainOK 28162 y332Arrays y332Words y332Base = true ∧
      ModelNative.chainSizes 28162 y332Arrays y332Words y332Base =
      [2, 28160, 3159, 288, 35, 12, 3, 2, 2] :=
  ⟨y332_size, y332_perms, y332_relators, y332_chain.1, y332_chain.2⟩

end Certificates
