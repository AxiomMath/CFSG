module

public import CFSG.Monster.GMS.Facts.BabyTables
public import CFSG.Monster.GMS.Facts.Basic

public section

namespace CFSG.Monster.GMS

open CFSG.Blueprint.NativeSporadic

variable {G : Type*} [Group G]

@[expose] def DoubleCoverThreeSwap (b : G) : Prop :=
  ∀ φ : Subgroup.centralizer ({b} : Set G) →* B, Function.Surjective φ →
    φ.ker.map (Subgroup.centralizer ({b} : Set G)).subtype = Subgroup.zpowers b →
    ∀ a c : Subgroup.centralizer ({b} : Set G), BabyInv 0 (φ a) → BabyInv 0 (φ c) →
      orderOf (φ a * φ c) = 3 →
        ∃ h ∈ Subgroup.centralizer ({b} : Set G),
          h * (a : G) * h⁻¹ = a * b ∧ h * (c : G) * h⁻¹ = c * b

@[expose] def DoubleCoverThreeSwapStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (b : G), IsTwoBabyCentralizer b → DoubleCoverThreeSwap b

@[expose] def DoubleCoverThreeSwapIn (G : Type*) [Group G] : Prop :=
  ∀ b : G, IsTwoBabyCentralizer b → DoubleCoverThreeSwap b

theorem DoubleCoverThreeSwapStatement.inG (h : DoubleCoverThreeSwapStatement) {G : Type}
    [Group G] [Finite G] : DoubleCoverThreeSwapIn G :=
  fun b hb => h G b hb

end CFSG.Monster.GMS
