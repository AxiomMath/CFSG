module

public import CFSG.Quasithin.Background.A4Defs
public import CFSG.LocalAnalysis.QuasithinUnique.PushingUp.Blocks

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

@[expose] def AutFactL2Block1521 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L P : Subgroup G), IsShort2 L →
    (∃ n : ℕ, 1 < n ∧ IsLin2Type L n) → IsSylowTwoOf P L →
    ∀ v : G, v ∈ Subgroup.normalizer (L : Set G) → IsPGroup 2 ↥(Subgroup.zpowers v) →
      (∀ b ∈ oTwoUpper (L ⊓ Subgroup.normalizer (P : Set G)), v * b = b * v) →
      ∀ l ∈ L, v * l = l * v

end CFSG.Quasithin
