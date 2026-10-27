module

public import Certificates.Kernel.F4Planes.WitGlue

@[expose] public section

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.RankThree.PartTwo.Sec4.RonanK432

public section

namespace Certificates

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.RankThree.PartTwo.Sec4.RonanK432 in
theorem certificate428003 :     ∀ (K : Type) [Field K] [Finite K], Nat.card K = 2 →
      ∀ a : adjointGroup .F4 K, a ≠ 1 → a ^ 3 = 1 →
        Wit3 (⊤ : Subgroup (adjointGroup .F4 K)) a :=
  CFSG.KC.F4Planes.wit3_F42

end Certificates
