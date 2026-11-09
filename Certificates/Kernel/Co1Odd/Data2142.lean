module

public import Init
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.NatItems
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.HexNat

public section

namespace CertificateChecks.KernelCo1Odd

#kc_repo #kc_nat_items CertificateChecks.KernelCo1Odd
  "Certificates/Kernel/Co1Odd/data/Data2142.items" 1595 9947021957113942399
  G[21]

#kc_repo #kc_json CertificateChecks.KernelCo1Odd
  "Certificates/Kernel/Co1Odd/data/Data2142.json" 1951 8950545775707599078
  (rowA : Nat) (rowC : Nat) (ATP : Nat) (STP : Nat) (CTP : Nat) (S1TP : Nat) (S2TP : Nat)
  (NS : Nat) (FA : List Nat) (YA : List Nat) (FC : List Nat) (YC : List Nat) (CL : List Nat)

@[expose] def tabText : String := include_str "data/tab2142.hex"

@[expose] noncomputable def TB : Nat := by hex_nat tabText 23040 12013028659483267121

@[expose] noncomputable def G : List Nat := [G0, G1, G2, G3, G4, G5, G6, G7, G8, G9, G10, G11, G12, G13, G14, G15, G16, G17, G18, G19, G20]

end CertificateChecks.KernelCo1Odd

end
