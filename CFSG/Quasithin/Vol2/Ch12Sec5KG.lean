module

public import CFSG.Foundations.Basic
public import CFSG.Quasithin.Background.A4Defs

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin

namespace S125KG

variable {X : Type} [Group X]

@[expose] def Config63 (S N D : Subgroup X) : Prop :=
  S ≤ D ∧ D ≤ N ∧ Nat.card N = 63 * Nat.card S ∧ Nat.card D = 3 * Nat.card S ∧
    ¬ D ≤ CFSG.inSubgroup CFSG.perfectResidual N ⊔ S

end S125KG

open S125KG

@[expose] def KG125GammaM24 : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (K₀ : Subgroup X) [K₀.Normal],
    Nonempty (↥K₀ ≃* NativeSporadic.M24) → Subgroup.centralizer (K₀ : Set X) ≤ K₀ →
    IsPGroup 2 (X ⧸ K₀) → ∀ S : Subgroup X, QuasithinUnique.IsSylowTwoOf S ⊤ →
      27 ∣ Nat.card ↥(sSup {H : Subgroup X | S ≤ H ∧ Group.IsSolvable ↥H})

@[expose] def KG125BetaJ4 : Prop :=
  ∀ (X : Type) [Group X] [Finite X], Nonempty (X ≃* NativeSporadic.J4) →
    ∀ S N D E : Subgroup X, QuasithinUnique.IsSylowTwoOf S ⊤ → Config63 S N D →
      E ≤ pCoreOf 2 N → N ≤ Subgroup.normalizer (E : Set X) → Nat.card E = 8 →
      ⁅CFSG.inSubgroup CFSG.perfectResidual (Subgroup.centralizer (E : Set X)),
          CFSG.inSubgroup CFSG.perfectResidual N⁆ ≤
          pCoreOf 2 (Subgroup.normalizer (E : Set X)) ∧
        oTwoUpper D ≤ CFSG.inSubgroup CFSG.perfectResidual (Subgroup.centralizer (E : Set X)) ⊔
          pCoreOf 2 (Subgroup.normalizer (E : Set X))

@[expose] def KG125GammaJ4 : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (K₀ : Subgroup X) [K₀.Normal],
    Nonempty (↥K₀ ≃* NativeSporadic.J4) → Subgroup.centralizer (K₀ : Set X) ≤ K₀ →
    IsPGroup 2 (X ⧸ K₀) → ∀ S : Subgroup X, QuasithinUnique.IsSylowTwoOf S ⊤ →
      27 ∣ Nat.card ↥(sSup {H : Subgroup X | S ≤ H ∧ Group.IsSolvable ↥H})

end CFSG.Quasithin.H13
