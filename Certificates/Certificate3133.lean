module

public import CFSG.Monster.B.GSide.EdgeQCertDCInputs

public section

open CFSG.Monster.B.GSide

namespace Certificates

open CFSG.Monster.B.GSide in
theorem certificate3133 : ∀ i l : Fin 15, bWcode (commCode i) (commY l) = if i = l then 1 else 0 :=
  by decide +kernel

end Certificates
