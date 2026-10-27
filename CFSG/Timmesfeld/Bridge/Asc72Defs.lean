module

public import CFSG.Adapters.QiuzhenLegacy.BenderSuzuki.Models
public import Mathlib.GroupTheory.SemidirectProduct
public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.Timmesfeld.Bridge.Asc72

variable {G : Type*} [Group G]

@[expose] def IsOddTransp (D : Set G) : Prop :=
  (∀ d ∈ D, orderOf d = 2) ∧ ∀ d ∈ D, ∀ e ∈ D, orderOf (d * e) ∣ 2 ∨ Odd (orderOf (d * e))

@[expose] def IsOddTranspClass (D : Set G) : Prop :=
  (∃ d₀ : G, D = {g | IsConj d₀ g}) ∧ IsOddTransp D ∧ Subgroup.closure D = ⊤

@[expose] def IsMinimalNormal (M : Subgroup G) : Prop :=
  M.Normal ∧ M ≠ ⊥ ∧ ∀ N : Subgroup G, N.Normal → N ≤ M → N = ⊥ ∨ N = M

@[expose] def WidthOne (X : Set G) : Prop :=
  ∀ S : Sylow 2 G, (X ∩ (S : Set G)).ncard = 1

@[expose] def permAct (ι L : Type*) [Group L] : Equiv.Perm ι →* MulAut (ι → L) where
  toFun σ := MulEquiv.arrowCongr σ (MulEquiv.refl L)
  map_one' := by
    ext h i
    rfl
  map_mul' σ τ := by
    ext h i
    rfl

abbrev L2Wreath (f n : ℕ) : Type :=
  (Fin n → CFSG.Theory.Comparator.PSL2Model f) ⋊[permAct (Fin n) (CFSG.Theory.Comparator.PSL2Model f)]
    Equiv.Perm (Fin n)

@[expose] def conjSet (M : Subgroup G) (u : G) : Set ↥(M ⊔ Subgroup.zpowers u) :=
  {k | ∃ m ∈ M, (k : G) = m * u * m⁻¹}

@[expose] def AlmostSimpleCase (G : Type*) [Group G] (D : Set G) : Prop :=
  ∃ (M : Subgroup G) (_ : M.Normal), IsMinimalNormal M ∧ (∀ N, IsMinimalNormal N → N = M) ∧
    IsSimpleGroup M ∧ Subgroup.centralizer (M : Set G) = ⊥ ∧ 2 < M.index ∧
    WidthOne (QuotientGroup.mk' M '' D) ∧ ∀ u ∈ D, IsOddTranspClass (conjSet M u)

@[expose] def Conclusion (G : Type*) [Group G] (D : Set G) : Prop :=
  CFSG.BenderSuzuki.IsBenderGroup G ∨
    (∃ f n : ℕ, 2 ≤ f ∧ (n = 3 ∨ n = 4) ∧ Nonempty (G ≃* L2Wreath f n)) ∨
    AlmostSimpleCase G D

@[expose] def TheoremOne : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (D : Set G), (∃ d₀ : G, D = {g | IsConj d₀ g}) →
    (∀ d ∈ D, orderOf d = 2) → (∀ d ∈ D, ∀ e ∈ D, orderOf (d * e) ∣ 2 ∨ Odd (orderOf (d * e))) →
    Subgroup.closure D = ⊤ → (∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥) →
    (∃ H : Subgroup G, H ≠ ⊤ ∧ (∃ u ∈ D, u ∈ H) ∧
      ∀ u ∈ D, u ∈ H → ∀ v ∈ D, Commute u v → v ∈ H) →
    Conclusion G D

end CFSG.Timmesfeld.Bridge.Asc72
