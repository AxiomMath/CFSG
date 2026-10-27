module

public import CFSG.RankThree.GF2n.Stroth80.Sec10Defs

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

@[expose] def Stroth101Statement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ),
    Sec10Hyp hc n → ∃ t : G, Good101 M Q Z B t

@[expose] def Stroth103aStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (s : G),
    Sec10Hyp hc n → Good101 M Q Z B s → SLMNat hc s 2 → ∃ y ∈ Q, Good103 M Q Z B (s * y)

@[expose] def Stroth103bStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ),
    Sec10Hyp hc n → (∀ s : G, Good101 M Q Z B s → ¬ SLMNat hc s 2) →
      ∀ t : G, Good101 M Q Z B t →
        Vt M (LB M Q B) B Z t = (Q ⊓ QB (Subgroup.zpowers t)) ⊔ Z

@[expose] def Stroth107Statement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ),
    Sec10Hyp hc n → n = 6 ∧ ∀ t : G, Good101 M Q Z B t → SLMNat hc t 3

@[expose] def Stroth108CoreStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (t : G),
    Sec10Hyp hc 6 → (∀ s : G, Good101 M Q Z B s → SLMNat hc s 3) → Good103 M Q Z B t → False

end CFSG.RankThree.GF2n.Stroth80
