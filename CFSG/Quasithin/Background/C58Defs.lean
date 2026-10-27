module

public import CFSG.Quasithin.Background.TwoReduced
public import CFSG.LocalAnalysis.QuasithinUnique.QTKECore

public section

namespace CFSG.Quasithin.C58

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

@[expose] def InputC512G64 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G → (∃ a b : G, a * b ≠ b * a) →
    quasithinIsQTKECat G →
    ∀ (X V S : Subgroup G) (a k : G),
      pCoreOf 2 X ≠ ⊥ → IsTwoReducedIn X V → IsSylowTwoOf S X →
      a ∈ S → a ^ 2 = 1 → Nat.card ↥⁅V, Subgroup.zpowers a⁆ = 2 →
      conjClosure ⁅V, Subgroup.zpowers a⁆ X = V →
      k ∈ X → k ^ 3 = 1 → k ∉ Subgroup.centralizer (V : Set G) →
      a * k * a⁻¹ * k ∈ Subgroup.centralizer (V : Set G) →
      S ≤ Subgroup.normalizer
        ((Subgroup.zpowers k ⊔ X ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) : Set G) →
      X = X ⊓ Subgroup.normalizer (S : Set G) ⊔ Subgroup.zpowers k →
      X ⊓ Subgroup.normalizer (S : Set G) ≤
        Subgroup.normalizer ((⁅V, Subgroup.zpowers k⁆ : Subgroup G) : Set G)

end CFSG.Quasithin.C58
