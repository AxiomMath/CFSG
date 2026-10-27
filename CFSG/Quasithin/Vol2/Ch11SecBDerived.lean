module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.Defs
public import CFSG.Quasithin.Background.E1Defs
public import CFSG.Quasithin.H13.Statements
public import CFSG.Quasithin.Vol2.Ch3Basic

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecB

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13

@[expose] def DerivedHallBorel : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M H : Subgroup G), IsSimpleGroup G →
    (∃ a b : G, a * b ≠ b * a) → QuasithinUnique.quasithinIsQTKECat G →
    quasithinIsSylowTwo T → InM T M → Subgroup.normalizer (T : Set G) ≤ M → IsHStar T M H →
    1 < E1.nParam H →
      ∃ B : Subgroup G, QuasithinUnique.Lin2.IsHallTwoPrimeOf B (H ⊓ M) ∧
        (∀ a ∈ B, ∀ b ∈ B, a * b = b * a) ∧
        T ≤ pCoreOf 2 (H ⊓ M) ⊔ (T ⊓ Subgroup.normalizer (B : Set G))

end CFSG.Quasithin.Vol2.Ch11.SecB
