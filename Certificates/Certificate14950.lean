module

public import Certificates.Kernel.F4Planes.Glue

@[expose] public section

open CFSG.Blueprint CFSG.Blueprint.Chevalley

public section

namespace Certificates

open CFSG.Blueprint CFSG.Blueprint.Chevalley in
theorem certificate14950 :     ∀ (K : Type) [Field K] [Finite K], Nat.card K = 2 →
      ∀ E : Subgroup (adjointGroup .F4 K), (∀ x ∈ E, x ^ 3 = 1) → Nat.card E = 3 ^ 2 →
        CFSG.LieType.SeitzGeneration.ExcHighThree.planeCl E = ⊤ :=
  CFSG.KC.F4Planes.planeCl_F42

end Certificates
