module

public import CFSG.Quasithin.Vol2.Ch10StatementsB

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecD

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13
open scoped MatrixGroups

@[expose] def FactSymFiveWrTwo : Prop :=
  (∀ N : Subgroup SymFiveWrTwo, N.Normal → N ≠ ⊥ →
      oTwoUpper (⊤ : Subgroup SymFiveWrTwo) ≤ N) ∧
    Subgroup.centralizer (oTwoUpper (⊤ : Subgroup SymFiveWrTwo) : Set SymFiveWrTwo) = ⊥

@[expose] def FactPSL2NormA5 : Prop :=
  ∀ p : ℕ, p.Prime → 7 ≤ p → ∀ A : Subgroup PSL(2, ZMod p),
    Nonempty (↥A ≃* alternatingGroup (Fin 5)) →
    ∀ B : Subgroup (MulAut PSL(2, ZMod p)), IsPGroup 2 B →
      (∀ b ∈ B, A.map (b : MulAut PSL(2, ZMod p)).toMonoidHom = A) → Nat.card B ≤ 4

@[expose] def FactAutSL : Prop :=
  ∀ k : ℕ, k = 4 ∨ k = 5 →
    Nat.card (MulAut (Matrix.SpecialLinearGroup (Fin k) (ZMod 2))) =
      2 * Nat.card (Matrix.SpecialLinearGroup (Fin k) (ZMod 2))

end CFSG.Quasithin.Vol2.Ch10.SecD
