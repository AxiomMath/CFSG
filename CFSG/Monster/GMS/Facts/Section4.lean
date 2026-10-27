module

public import CFSG.Monster.GMS.Facts.Section36
public import CFSG.Monster.GMS.Facts.Co1Local

public section

namespace CFSG.Monster.GMS

open CFSG.Blueprint.NativeSporadic

@[expose] def TwoBabyUnique : Prop :=
  ∀ (G G' : Type) [Group G] [Group G'] [Finite G] [Finite G'] (a : G) (a' : G'),
    IsTwoBabyCentralizer a → IsTwoBabyCentralizer a' →
      Nonempty (Subgroup.centralizer ({a} : Set G) ≃* Subgroup.centralizer ({a'} : Set G'))

section Group

variable {G : Type*} [Group G]

@[expose] def EightGroupExists (a z₀ : G) : Prop :=
  ∀ x y : G, IsLineTriple a x y → ∀ n : ℕ, (n = 1 ∨ n = 3 ∨ n = 4) →
    ∃ t : G, IsEightExt x y t ∧ twoBCount z₀ x y t = n

end Group

@[expose] def Co2StabFacts : Prop :=
  ∀ v ∈ co1Orbit 0, ∀ H : Subgroup Co1, H ≤ co1Stab v → Nat.card (co1Stab v) ≤ 2 * Nat.card H →
    ∀ N : Subgroup Co1, N ≤ H → (∀ h ∈ H, ∀ n ∈ N, h * n * h⁻¹ ∈ N) → IsPGroup 2 N → N = ⊥

end CFSG.Monster.GMS
