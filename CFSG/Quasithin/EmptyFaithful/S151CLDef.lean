module

public import CFSG.Quasithin.EmptyFaithful.S151XF

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank

@[expose] def CompListNoL32 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M Z₁ Z₂ V₁ V₂ L : Subgroup G),
    Ctx15120 T Mc M Z₁ Z₂ V₁ V₂ L → IsComponentOf L (g1_1516 Z₁) →
    ¬ (IsPSL 3 2 1 ↥L ∨ IsPSL 2 7 1 ↥L)

@[expose] def CompListNoA6 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M Z₁ Z₂ V₁ V₂ L : Subgroup G),
    Ctx15120 T Mc M Z₁ Z₂ V₁ V₂ L → IsComponentOf L (g1_1516 Z₁) →
    Lemma15118Extra T Mc M Z₁ → ¬ IsAlt 6 ↥L

@[expose] def CompListNoA7 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M Z₁ Z₂ V₁ V₂ L : Subgroup G),
    Ctx15120 T Mc M Z₁ Z₂ V₁ V₂ L → IsComponentOf L (g1_1516 Z₁) →
    Lemma15118Extra T Mc M Z₁ → ¬ IsAlt 7 ↥L

@[expose] def CompListNoG2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M Z₁ Z₂ V₁ V₂ L : Subgroup G),
    Ctx15120 T Mc M Z₁ Z₂ V₁ V₂ L → IsComponentOf L (g1_1516 Z₁) →
    (∀ n : ℕ, 2 ≤ n → ¬ IsG2 2 n ↥L) ∧ ¬ IsG2 2 2 (↥L ⧸ CFSG.pCore 2 ↥L)

@[expose] def CompListNo3D4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M Z₁ Z₂ V₁ V₂ L : Subgroup G),
    Ctx15120 T Mc M Z₁ Z₂ V₁ V₂ L → IsComponentOf L (g1_1516 Z₁) →
    ∀ n : ℕ, 2 ≤ n → ¬ Is3D4 2 n ↥L

@[expose] def CompListNo2F4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M Z₁ Z₂ V₁ V₂ L : Subgroup G),
    Ctx15120 T Mc M Z₁ Z₂ V₁ V₂ L → IsComponentOf L (g1_1516 Z₁) →
    ∀ n : ℕ, Odd n → 3 ≤ n → ¬ Is2F4 n ↥L

@[expose] def CompListNoJ4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M Z₁ Z₂ V₁ V₂ L : Subgroup G),
    Ctx15120 T Mc M Z₁ Z₂ V₁ V₂ L → IsComponentOf L (g1_1516 Z₁) →
    ¬ IsSporadic .J4 (↥L ⧸ CFSG.pCore 2 ↥L)

@[expose] def CompListNoL33 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M Z₁ Z₂ V₁ V₂ L : Subgroup G),
    Ctx15120 T Mc M Z₁ Z₂ V₁ V₂ L → IsComponentOf L (g1_1516 Z₁) → ¬ IsPSL 3 3 1 ↥L

@[expose] def CompListNoL2p : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M Z₁ Z₂ V₁ V₂ L : Subgroup G),
    Ctx15120 T Mc M Z₁ Z₂ V₁ V₂ L → IsComponentOf L (g1_1516 Z₁) →
    ∀ p : ℕ, CFSG.QuasithinUnique.Ch1.IsFermatOrMersennePrime p → 7 < p → ¬ IsPSL 2 p 1 ↥L

end CFSG.Quasithin
