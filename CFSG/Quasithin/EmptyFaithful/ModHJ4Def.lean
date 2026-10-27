module

public import CFSG.LocalAnalysis.QuasithinUnique.Defs
public import CFSG.Blueprint.NativeSporadic

public section

namespace CFSG.Quasithin.ModH

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Blueprint

@[expose] def IsTwoLocalSub {Q : Type} [Group Q] (M : Subgroup Q) : Prop :=
  M ≠ ⊤ ∧ ∃ N : Subgroup Q, IsPGroup 2 ↥N ∧ N ≠ ⊥ ∧ Subgroup.normalizer (N : Set Q) = M

@[expose] def IsMaxTwoLocal {Q : Type} [Group Q] (M : Subgroup Q) : Prop :=
  IsTwoLocalSub M ∧ ∀ M' : Subgroup Q, IsTwoLocalSub M' → M ≤ M' → M' = M

@[expose] def FactJ4TwoLocals2 : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q], Nonempty (Q ≃* NativeSporadic.Carrier .J4) →
    ∀ S : Subgroup Q, IsSylowTwoOf S ⊤ →
      ∀ M : Subgroup Q, IsMaxTwoLocal M → S ≤ M → ∀ R : Subgroup Q,
        M ≤ Subgroup.normalizer (R : Set Q) → R ≤ M → Group.IsSolvable ↥R → ¬ 9 ∣ Nat.card ↥R

end CFSG.Quasithin.ModH
