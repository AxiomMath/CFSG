module

public import CFSG.Quasithin.Background.A3StructureDefs

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin

@[expose] def FactHatA7Loc12626 : Prop :=
  ∀ (X : Type) [Group X] [Finite X], IsHat X (alternatingGroup (Fin 7)) →
    (∀ s : X, s ^ 3 ∈ Subgroup.center X → s ^ 3 = 1) ∧
    (∀ α : MulAut X, (Odd (orderOf α) ∨ ∃ P : Subgroup X, Nat.card P = 9 ∧ ∀ x ∈ P, α x = x) →
      α ∈ (MulAut.conj : X →* MulAut X).range) ∧
    (∀ k : X, k ^ 2 = 1 → k ≠ 1 → ∃ E : Subgroup X, IsElemAbelian 3 E ∧ Nat.card E = 9 ∧
      ∀ x : X, x * k = k * x → Odd (orderOf x) → x ∈ E) ∧
    ∀ E : Subgroup X, IsElemAbelian 3 E → Nat.card E = 9 → Subgroup.center X ≤ E →
      ∃ A S : Subgroup X, IsPGroup 2 A ∧ A ≤ Subgroup.centralizer (E : Set X) ∧
        (∀ x ∈ Subgroup.centralizer (E : Set X), (∃ n : ℕ, x ^ 2 ^ n = 1) → x ∈ A) ∧
        IsPGroup 3 S ∧ Nat.card S = 27 ∧ S ≤ Subgroup.normalizer (A : Set X)

end CFSG.Quasithin.H13
