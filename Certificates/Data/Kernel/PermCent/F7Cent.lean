module

public import Certificates.Data.Kernel.PermCent.AllPermsC
public import Certificates.Data.Kernel.PermCent.SmallK

public section

namespace CFSG.Certificates.Kernel.PkCV

@[expose] def forceQL {m k : Nat} {β : Sort _} :
    List (CV m × CV k) → (List (CV m × CV k) → β) → β
  | [], c => c []
  | a :: l, c => forceC a.1 fun x => forceC a.2 fun y => forceQL l fun l => c ((x, y) :: l)

@[expose] noncomputable def CF7 (ρ : CV 7) : List (CV 7 × CV 4) :=
  forcePL (allPermsP 7 inferInstance) fun L => forcePL DLP fun D =>
    (L.filter fun x => eq22C x.1 ρ ρ x.1).flatMap fun x =>
      (D.filter fun y => x.2 == y.2).map fun y => (x.1, y.1)

end CFSG.Certificates.Kernel.PkCV

end
