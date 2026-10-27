module

public import CFSG.Open.QuasithinDefs
public import CFSG.Blueprint.Catalog

public section

namespace CFSG.Quasithin.G23Type

open CFSG.Open CFSG.Blueprint
open scoped MatrixGroups

variable {G : Type*} [Group G]

structure G23One (H H₁ H₂ : Subgroup G) : Prop where
  le_one : H₁ ≤ H
  le_two : H₂ ≤ H
  normal_one : H ≤ Subgroup.normalizer (H₁ : Set G)
  normal_two : H ≤ Subgroup.normalizer (H₂ : Set G)
  iso_one : Nonempty (↥H₁ ≃* SL(2, ZMod 3))
  iso_two : Nonempty (↥H₂ ≃* SL(2, ZMod 3))
  index : (H₁ ⊔ H₂).relIndex H = 2
  card_inf : Nat.card ↥(H₁ ⊓ H₂) = 2
  eq_centralizer : H = Subgroup.centralizer ((H₁ ⊓ H₂ : Subgroup G) : Set G)

structure G23Two (M : Subgroup G) : Prop where
  elem : IsElemAbelian 2 (quasithinGenFitting M)
  card : Nat.card ↥(quasithinGenFitting M) = 8
  quot : ∃ θ : ↥M →* SL(3, ZMod 2), Function.Surjective θ ∧
    θ.ker = (quasithinGenFitting M).subgroupOf M

@[expose] def IsG23Type (G : Type*) [Group G] : Prop :=
  ∃ H H₁ H₂ M : Subgroup G, G23One H H₁ H₂ ∧ G23Two M

@[expose] def StatementI45 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsG23Type G → LieModel G .G2 0 3 1

end CFSG.Quasithin.G23Type
