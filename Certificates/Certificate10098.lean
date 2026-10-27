module

public import CFSG.YGroups.Exact.Y322Inputs
public import CFSG.YGroups.Defs
import Certificates.Kernel.YModel.Y322

public section

namespace Certificates

open CertificateChecks.KernelYModel

open CFSG.YGroups in
theorem certificate10098 :
    y322Arrays.size = 8 ∧
      ModelNative.permsOK 728 y322Arrays = true ∧
      ModelNative.relatorsOK 728 y322Arrays (yRels 3 2 2) = true ∧
      ModelNative.chainOK 728 y322Arrays y322Words y322Base = true ∧
      ModelNative.chainSizes 728 y322Arrays y322Words y322Base =
      [728, 243, 72, 20, 9, 2, 2] :=
  ⟨y322_size, y322_perms, y322_relators, y322_chain0.1, y322_chain0.2⟩

end Certificates
