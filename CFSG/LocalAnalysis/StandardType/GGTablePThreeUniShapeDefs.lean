module

public import CFSG.LocalAnalysis.StandardType.GGTablePThreeLinDefs
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeUniModel

public section

namespace CFSG.StandardType.TablePThreeKG

open CFSG CFSG.Assembly

@[expose] def UniShapeConcl {X : Type} [Group X] (q N : ℕ) (A : Subgroup (MulAut X)) (J : Subgroup X) :
    Prop :=
  (∃ (F : Type) (_ : Field F) (_ : Finite F) (j : ℕ), (j = 1 ∨ j = 3) ∧ Nat.card F = q ^ j ∧
      4 ≤ Nat.card F ∧ Nonempty (J ⧸ Subgroup.center J ≃* PSLg 2 F) ∧
      (j = 1 → Nat.card A < 3 ^ 3) ∧ (j = 3 → N = 6 ∧ Nat.card A ≤ 3 ^ 3)) ∨
    ∃ (E : Type) (_ : Field E) (_ : Finite E) (m j : ℕ), (j = 1 ∨ j = 3) ∧
      Nat.card E = (q ^ j) ^ 2 ∧ 3 ≤ m ∧ (m, q ^ j) ≠ (3, 2) ∧
      Nonempty (J ⧸ Subgroup.center J ≃* PSUg m E (q ^ j)) ∧
      (j = 1 → m < N) ∧ (j = 3 → N = 3 * m) ∧
      (m = 3 → j = 1 → Subgroup.center J ≠ ⊥ ∧ Nat.card A ≤ 3 ^ 3 ∧ N ≤ 5)

end CFSG.StandardType.TablePThreeKG

end
