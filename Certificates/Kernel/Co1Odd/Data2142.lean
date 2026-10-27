module

public import Init
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.NatItemsGz
import CFSG.Certificates.Kernel.Common.Repo

public section

namespace CertificateChecks.KernelCo1Odd

#kc_repo #kc_nat_items_gz CertificateChecks.KernelCo1Odd
  "Certificates/Kernel/Co1Odd/data/Data2142.items.gz" 1595 9947021957113942399
  G[21]

#kc_repo #kc_json_gz CertificateChecks.KernelCo1Odd
  "Certificates/Kernel/Co1Odd/data/Data2142.json.gz" 1951 8950545775707599078
  (rowA : Nat) (rowC : Nat) (ATP : Nat) (STP : Nat) (CTP : Nat) (S1TP : Nat) (S2TP : Nat)
  (NS : Nat) (FA : List Nat) (YA : List Nat) (FC : List Nat) (YC : List Nat) (CL : List Nat)

@[expose] noncomputable def G : List Nat := [G0, G1, G2, G3, G4, G5, G6, G7, G8, G9, G10, G11, G12, G13, G14, G15, G16, G17, G18, G19, G20]

end CertificateChecks.KernelCo1Odd

end
