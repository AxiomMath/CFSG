module

public import CFSG.LocalAnalysis.StandardType.GGTablePThreeSplit

public section

namespace CFSG.StandardType.TablePThreeKG

open CFSG CFSG.Assembly

abbrev PSLg (m : ℕ) (E : Type) [Field E] : Type :=
  LargeEvenProj (LargeEvenSLGroup (Fin m) E)

@[expose] def LinShapeConcl {X : Type} [Group X] (q N : ℕ) (A : Subgroup (MulAut X))
    (J : Subgroup X) : Prop :=
  ∃ (E : Type) (_ : Field E) (_ : Finite E) (m j : ℕ),
    2 ≤ m ∧ (m = 2 → 4 ≤ Nat.card E) ∧ 1 ≤ j ∧ j ≤ 3 ∧ Nat.card E = q ^ j ∧ j * m ≤ N ∧
    Nonempty (J ⧸ Subgroup.center J ≃* PSLg m E) ∧
    (j = 3 → 3 ∣ q - 1 ∧ N = 3 * m) ∧ (j = 2 → q = 2) ∧
    (m = 3 → (j = 1 ∧ 3 ∣ q - 1 ∨ j = 2) → Subgroup.center J ≠ ⊥) ∧
    (m = 2 → (j = 3 → Nat.card A ≤ 3 ^ 3) ∧ (j ≠ 3 → Nat.card A < 3 ^ 3))

@[expose] def LinJ (J : Type) [Group J] (m : ℕ) (E : Type) [Field E] : Prop :=
  2 ≤ m ∧ (m = 2 → 4 ≤ Nat.card E) ∧ Nonempty (J ⧸ Subgroup.center J ≃* PSLg m E)

end CFSG.StandardType.TablePThreeKG

end
