module

public import CFSG.Open.Defs

public section

namespace CFSG.Open
variable {G : Type*} [Group G]

@[expose] def lBalanceIsKGroup (X : Type*) [Group X] : Prop :=
  IsKGroup X

@[expose] def lBalancePrimeCore (p : ℕ) (Y : Subgroup G) : Subgroup G :=
  sSup {N | N ≤ Y ∧ (N.subgroupOf Y).Normal ∧ Nat.Coprime p (Nat.card N)}

@[expose] def lBalanceIsComponentLift (p : ℕ) (Y K : Subgroup G) : Prop :=
  lBalancePrimeCore p Y ≤ K ∧ IsSubnormal K Y ∧
    ∃ _ : ((lBalancePrimeCore p Y).subgroupOf K).Normal,
      IsQuasisimple (K ⧸ (lBalancePrimeCore p Y).subgroupOf K)

@[expose] def lBalanceIsPComponent (p : ℕ) (Y L : Subgroup G) : Prop :=
  IsSubnormal L Y ∧ lBalanceIsComponentLift p Y (L ⊔ lBalancePrimeCore p Y) ∧
    ∀ J : Subgroup G, J < L → IsSubnormal J Y →
      J ⊔ lBalancePrimeCore p Y ≠ L ⊔ lBalancePrimeCore p Y

@[expose] def lBalancePLayer (p : ℕ) (Y : Subgroup G) : Subgroup G :=
  sSup {L | lBalanceIsPComponent p Y L}

@[expose] def LBalanceStatement : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (_ : lBalanceIsKGroup X)
    (p : ℕ) (_ : p.Prime) (P : Subgroup X) (_ : IsPGroup p P),
    lBalancePLayer p (Subgroup.normalizer (P : Set X)) ≤ lBalancePLayer p ⊤ ∧
      lBalancePLayer p (Subgroup.centralizer (P : Set X)) ≤ lBalancePLayer p ⊤ ∧
      (lBalancePrimeCore p (⊤ : Subgroup X) = ⊥ →
        ∀ a ∈ lBalancePLayer p (Subgroup.normalizer (P : Set X)),
          ∀ b ∈ lBalancePrimeCore p (Subgroup.normalizer (P : Set X)), a * b = b * a)

end CFSG.Open
