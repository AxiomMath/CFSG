module

public import CFSG.Blueprint.Catalog
public import CFSG.Foundations.Basic

public section

namespace CFSG.Quasithin.H13.QTESylow

open CFSG.Blueprint CFSG.Assembly.LowTwoRank
open scoped Pointwise

@[expose] def StmtCatalogNoncyclicPrimeSylowProduct : Prop :=
  ∀ (S : Type) [Group S] [Finite S] [IsSimpleGroup S], (∃ a b : S, a * b ≠ b * a) →
    Catalog S → CFSG.IsStronglyQuasithin S →
    ∀ p : ℕ, p.Prime → 5 ≤ p → ∀ (T : Sylow 2 S) (P : Subgroup S), IsPGroup p P →
      ¬ IsCyclic P → (P : Set S) * (T : Set S) = (T : Set S) * (P : Set S) →
      (∃ ℓ : ℕ, ℓ.Prime ∧ 5 ≤ ℓ ∧
          (StatedClassicalModel S .PSL 3 ℓ 1 ∨ StatedClassicalModel S .PSU 3 ℓ 1)) ∨
        (∃ f : ℕ, 3 ≤ f ∧ StatedClassicalModel S .PSL 3 2 f) ∨
        (∃ f : ℕ, 2 ≤ f ∧ StatedClassicalModel S .PSp 2 2 f) ∨
        ((∃ f : ℕ, 2 ≤ f ∧ ChevalleyExceptionalModel S .G2 2 f) ∨
          ∃ f : ℕ, 1 ≤ f ∧ ChevalleyExceptionalModel S .trialityD4 2 f) ∨
        ((∃ a : ℕ, 1 ≤ a ∧ ReeTitsModel S .twistedF4 2 (2 * a + 1)) ∨
          ReeTitsModel S .Tits 2 1) ∨
        (Nonempty (S ≃* NativeSporadic.J4) ∧ p = 11)

end CFSG.Quasithin.H13.QTESylow
