
module


public import Certificates.Kernel.F4Planes.E6Glue

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.SeitzGeneration.ExcHighThree

public section

namespace Certificates

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.SeitzGeneration.ExcHighThree in
theorem certificate14949 :     ∀ (K : Type) [Field K] [Finite K], Nat.card K = 2 →
      ∀ E₃ : Subgroup (adjointGroup .F4 K), (∀ x ∈ E₃, x ^ 3 = 1) → Nat.card E₃ = 3 ^ 2 →
        ∃ e ∈ E₃, e ≠ 1 ∧ Subgroup.closure (((embE6F4 K).range : Set (adjointGroup .E6 K)) ∪
          (Subgroup.centralizer ({embE6F4 K e} : Set (adjointGroup .E6 K)) :
            Set (adjointGroup .E6 K))) = ⊤ :=
  CFSG.KC.F4PlanesE6.e6CloseAtTwo_kernel

end Certificates
