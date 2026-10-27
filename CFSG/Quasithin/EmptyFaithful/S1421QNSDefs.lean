module

public import CFSG.Quasithin.EmptyFaithful.S1421F112

public section

namespace CFSG.Quasithin

@[expose] def AutQ8D8Facts : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q], IsQ8D8 Q →
    ¬ 7 ∣ Nat.card (MulAut Q) ∧ ¬ 17 ∣ Nat.card (MulAut Q) ∧
      ¬ ∃ E : Subgroup (MulAut Q), Nat.card E = 25

@[expose] def AutExt9Facts : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q], IsSpecialPow 2 2 4 Q →
    ¬ 13 ∣ Nat.card (MulAut Q) ∧ ¬ 73 ∣ Nat.card (MulAut Q) ∧
      ¬ ∃ E : Subgroup (MulAut Q), Nat.card E = 49

end CFSG.Quasithin
