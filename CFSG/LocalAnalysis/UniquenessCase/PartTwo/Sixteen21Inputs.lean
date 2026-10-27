module

public import CFSG.Open.StatedDefs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open

namespace Sixteen21

@[expose] def RSU4NatFix : Prop :=
  ∀ (K : Type) [Field K] [Finite K], Nat.card K = 4 →
    ∀ x : Fin 4 → K, ∃ g ∈ StatedSU 4 2 K, orderOf g = 3 ∧
      Matrix.mulVec (g : Matrix (Fin 4) (Fin 4) K) x = x

@[expose] def RSp6SmallIndex : Prop :=
  ∀ (K : Type) [Field K] [Finite K], Nat.card K = 2 →
    ∀ H : Subgroup ↥(StatedSp 3 K), H.index ≤ 255 → 3 ∣ Nat.card H

end Sixteen21

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
