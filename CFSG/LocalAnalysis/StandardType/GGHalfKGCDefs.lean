module

public import Mathlib.FieldTheory.Finite.GaloisField

public section

namespace CFSG.StandardType

@[expose] def GGKGCCentSolv (P : Type) [Group P] (n : ℕ) : Prop :=
  ∀ (J : Subgroup P) (k : P),
    Nonempty (↥J ≃* Matrix.SpecialLinearGroup (Fin (n - 1)) (GaloisField 2 1)) →
    k ^ 3 = 1 → k ≠ 1 → k ∈ Subgroup.centralizer (J : Set P) →
    Group.IsSolvable ↥(Subgroup.centralizer (J : Set P))

end CFSG.StandardType

end
