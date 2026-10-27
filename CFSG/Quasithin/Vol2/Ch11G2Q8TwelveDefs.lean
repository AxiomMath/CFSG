module

public import CFSG.Quasithin.Vol2.Ch11SecBFacts22G

public section

namespace CFSG.Quasithin.Vol2.Ch11.G2Q8

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.Quasithin.Vol2.Ch11.SecB

@[expose] def FactG2TwelveCent : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L V X T V₁ V₃ : Subgroup G) (n : ℕ)
    (hV : IsElemAbelian 2 V),
    2 ≤ n → L ≤ Subgroup.normalizer (V : Set G) → ⁅V, L⁆ = V → NatModuleOf L V n →
    KindG2 L V n → V ⊓ Subgroup.centralizer (L : Set G) = ⊥ → L ≤ X →
    X ⊓ Subgroup.normalizer (V : Set G) ≤ Subgroup.normalizer (L : Set G) →
    QuasithinUnique.IsSylowTwoOf T (L ⊔ T) → T ≤ Subgroup.normalizer (V : Set G) →
    T ≤ Subgroup.normalizer (L : Set G) →
    V ⊓ Subgroup.centralizer (L : Set G) ≤ V₁ → V₁ ≤ V₃ → V₃ ≤ V →
    IsEndStable L V (V ⊓ Subgroup.centralizer (L : Set G)) V₁ →
    IsEndStable L V (V ⊓ Subgroup.centralizer (L : Set G)) V₃ →
    (V ⊓ Subgroup.centralizer (L : Set G)).relIndex V₁ = 2 ^ n →
    (V ⊓ Subgroup.centralizer (L : Set G)).relIndex V₃ = 2 ^ (n * 3) →
    T ≤ Subgroup.normalizer (V₁ : Set G) → T ≤ Subgroup.normalizer (V₃ : Set G) →
    ∀ A : Subgroup G, A ≤ pCoreOf 2 (LOf L V₁ ⊔ T) →
      autI hV A ∈ E3.aSet (2 * n - 1) (autI hV X) →
        A ≤ Subgroup.centralizer (V₃ : Set G)

@[expose] def FactG2TwelveRad : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L V X T V₁ V₃ : Subgroup G) (n : ℕ)
    (hV : IsElemAbelian 2 V),
    2 ≤ n → L ≤ Subgroup.normalizer (V : Set G) → ⁅V, L⁆ = V → NatModuleOf L V n →
    KindG2 L V n → V ⊓ Subgroup.centralizer (L : Set G) ≠ ⊥ → L ≤ X →
    X ⊓ Subgroup.normalizer (V : Set G) ≤ Subgroup.normalizer (L : Set G) →
    QuasithinUnique.IsSylowTwoOf T (L ⊔ T) → T ≤ Subgroup.normalizer (V : Set G) →
    T ≤ Subgroup.normalizer (L : Set G) →
    V ⊓ Subgroup.centralizer (L : Set G) ≤ V₁ → V₁ ≤ V₃ → V₃ ≤ V →
    IsEndStable L V (V ⊓ Subgroup.centralizer (L : Set G)) V₁ →
    IsEndStable L V (V ⊓ Subgroup.centralizer (L : Set G)) V₃ →
    (V ⊓ Subgroup.centralizer (L : Set G)).relIndex V₁ = 2 ^ n →
    (V ⊓ Subgroup.centralizer (L : Set G)).relIndex V₃ = 2 ^ (n * 3) →
    T ≤ Subgroup.normalizer (V₁ : Set G) → T ≤ Subgroup.normalizer (V₃ : Set G) →
    ∀ A : Subgroup G, A ≤ pCoreOf 2 (LOf L V₁ ⊔ T) →
      autI hV A ∈ E3.aSet (2 * n - 1) (autI hV X) →
        A ≤ Subgroup.centralizer (V₃ : Set G)

theorem factG2Twelve_of (hC : FactG2TwelveCent) (hR : FactG2TwelveRad) : FactG2Twelve := by
  intro G _ _ L V X T V₁ V₃ n hV hn hLV hVL hnat hkind
  by_cases hCV : V ⊓ Subgroup.centralizer (L : Set G) = ⊥
  · exact hC G L V X T V₁ V₃ n hV hn hLV hVL hnat hkind hCV
  · exact hR G L V X T V₁ V₃ n hV hn hLV hVL hnat hkind hCV

end CFSG.Quasithin.Vol2.Ch11.G2Q8
