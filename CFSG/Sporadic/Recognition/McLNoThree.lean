module

public import CFSG.Blueprint.NativeSporadic

public section

namespace CFSG.Sporadic.Recognition.McLAS

@[expose] def McLNoThreeNormalized : Prop :=
  ∀ (Q : Type) [Group Q], Nonempty (Q ≃* CFSG.Blueprint.NativeSporadic.McL) →
    ∀ S : Subgroup Q, Nat.card ↥S = 2 ^ 7 →
      ∀ W : Subgroup Q, IsPGroup 3 ↥W → S ≤ Subgroup.normalizer (W : Set Q) → W = ⊥

end CFSG.Sporadic.Recognition.McLAS
