module

public import CFSG.YGroups.Exact.Y432Inputs
public import CFSG.YGroups.Defs
import Certificates.Kernel.YModel.Y432

public section

namespace Certificates

open CertificateChecks.KernelYModel

open CFSG.YGroups in
theorem certificate10100 :
    y432Arrays.size = 10 ∧
      ModelNative.permsOK 31673 y432Arrays = true ∧
      ModelNative.relatorsOK 31673 y432Arrays (yRels 4 3 2) = true ∧
      ModelNative.chainOK 31673 y432Arrays y432Words y432Base = true ∧
      ModelNative.chainSizes 31673 y432Arrays y432Words y432Base =
      [2, 31671, 28160, 3159, 288, 35, 12, 3, 2, 2] :=
  ⟨y432_size, y432_perms, y432_relators, y432_chain0.1, y432_chain0.2⟩

end Certificates
