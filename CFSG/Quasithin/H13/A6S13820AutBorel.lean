module

public import CFSG.Quasithin.Background.A3StructureDefs

public section

namespace CFSG.Quasithin.H13.A6

open CFSG.QuasithinUnique CFSG.Quasithin

@[expose] def BorelAut13820 {Q : Type} [Group Q] (S C : Subgroup Q) (α : MulAut Q) : Prop :=
  IsSylowTwoOf S ⊤ ∧ S ≤ C ∧ C ≤ Subgroup.normalizer (S : Set Q) ∧
    (C.subgroupOf (Subgroup.normalizer (S : Set Q))).Normal ∧
    C.relIndex (Subgroup.normalizer (S : Set Q)) ∣ 3 ∧
    (∃ k : ℕ, α ^ 2 ^ k = 1) ∧ S.map α.toMonoidHom = S ∧ ∀ c ∈ C, c⁻¹ * α c ∈ S

@[expose] def AutBorel13820L2 : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q] (n : ℕ), CFSG.IsQuasisimple Q →
    Odd (Nat.card (Subgroup.center Q)) → 2 ≤ n → IsPSL 2 2 n (Q ⧸ Subgroup.center Q) →
    ∀ (S C : Subgroup Q) (α : MulAut Q), BorelAut13820 S C α →
      (∃ g : Q, α = MulAut.conj g) ∨ n = 2

@[expose] def AutBorel13820L3 : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q] (n : ℕ), CFSG.IsQuasisimple Q →
    Odd (Nat.card (Subgroup.center Q)) → 2 ≤ n → IsPSL 3 2 n (Q ⧸ Subgroup.center Q) →
    ∀ (S C : Subgroup Q) (α : MulAut Q), BorelAut13820 S C α →
      (∃ g : Q, α = MulAut.conj g) ∨ n = 2

@[expose] def AutBorel13820U3 : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q] (n : ℕ), CFSG.IsQuasisimple Q →
    Odd (Nat.card (Subgroup.center Q)) → 2 ≤ n → IsPSU 3 2 n (Q ⧸ Subgroup.center Q) →
    ∀ (S C : Subgroup Q) (α : MulAut Q), BorelAut13820 S C α →
      (∃ g : Q, α = MulAut.conj g) ∨ n = 3

@[expose] def AutBorel13820Sp4 : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q] (n : ℕ), CFSG.IsQuasisimple Q →
    Odd (Nat.card (Subgroup.center Q)) → 2 ≤ n → IsPSp4 2 n (Q ⧸ Subgroup.center Q) →
    ∀ (S C : Subgroup Q) (α : MulAut Q), BorelAut13820 S C α → ∃ g : Q, α = MulAut.conj g

@[expose] def AutBorel13820G2 : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q] (n : ℕ), CFSG.IsQuasisimple Q →
    Odd (Nat.card (Subgroup.center Q)) → 2 ≤ n → IsG2 2 n (Q ⧸ Subgroup.center Q) →
    ∀ (S C : Subgroup Q) (α : MulAut Q), BorelAut13820 S C α → ∃ g : Q, α = MulAut.conj g

end CFSG.Quasithin.H13.A6
