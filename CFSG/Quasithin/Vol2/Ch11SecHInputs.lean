module

public import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecH

@[expose] def AS_I_1_3_L2 : Prop :=
  ∀ (n : ℕ), 2 ≤ n → ∀ (F : Type) [Field F] [Finite F], Nat.card F = 2 ^ n →
    ∀ (X : Type) [Group X] [Finite X], Group.IsPerfect X →
    ∀ (Z : Subgroup X) [Z.Normal], Z ≤ Subgroup.center X →
      Nonempty (X ⧸ Z ≃* Matrix.SpecialLinearGroup (Fin 2) F) →
        Z = ⊥ ∨ (n = 2 ∧ Nat.card Z = 2 ∧ ∀ x : X, x ^ 2 = 1 → x ∈ Z)

end CFSG.Quasithin.Vol2.Ch11.SecH
