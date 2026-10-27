module

public import CFSG.Quasithin.EmptyFaithful.S141
public import CFSG.Quasithin.EmptyFaithful.S1417System
public import CFSG.Quasithin.Background.B6Defs
public import CFSG.Quasithin.Background.A4Defs
public import CFSG.Quasithin.Background.B2FactorizationBridge
public import CFSG.Quasithin.Background.A3ComponentsBasic
public import CFSG.Quasithin.EmptyFaithful.Vocabulary

public section

open CFSG.QuasithinUnique (quasithinIsQTKECat)

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

@[expose] def StageLemma1414 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T : Subgroup G), IsSimpleGroup G →
    (∃ a b : G, a * b ≠ b * a) → quasithinIsQTKECat G → quasithinIsSylowTwo T →
    (∀ L : Subgroup G, ¬ quasithinIsFaithfulLocal T L) →
    ∀ M : Subgroup G, IsOrdMaximal T M → thompsonJ T ≤ M ⊓ Subgroup.centralizer (VZ T M : Set G) →
      IsGreatestOrd T M

@[expose] def Theorem311 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T : Subgroup G), IsSimpleGroup G →
    (∃ a b : G, a * b ≠ b * a) → quasithinIsQTKECat G → quasithinIsSylowTwo T →
    ∀ M₀ H R : Subgroup G, InH T M₀ → InH T H → (∃ N : Subgroup G, IsUniqueMaxOver H T N) →
      R ≠ ⊥ → R ≤ T → IsSylowTwoOf R (oTwoUpper H ⊔ R) →
      M₀ ≤ Subgroup.normalizer (R : Set G) →
      ∃ R₀ : Subgroup G, R₀ ≠ ⊥ ∧ R₀ ≤ R ∧ M₀ ⊔ H ≤ Subgroup.normalizer (R₀ : Set G)

@[expose] def Step1414B610 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T : Subgroup G), IsSimpleGroup G →
    (∃ a b : G, a * b ≠ b * a) → quasithinIsQTKECat G → quasithinIsSylowTwo T →
    (∀ L : Subgroup G, ¬ quasithinIsFaithfulLocal T L) →
    ∀ M₁ : Subgroup G, InM T M₁ → ¬ thompsonJ T ≤ Subgroup.centralizer (VZ T M₁ : Set G) →
      perfectCore M₁ ≤ Subgroup.centralizer (VZ T M₁ : Set G) →
      (∃ (hVe : IsElemAbelian 2 (VZ T M₁))
          (I : Finset (Subgroup (MulAut (IntMod (VZ T M₁) hVe)))),
        S1417.BlockSystem (autI hVe M₁) (autI hVe (thompsonJ M₁)) I ∧ I.card ≤ 2) →
      ∀ P : Subgroup G, P ∈ uFamHat (twoPrimeResidual (thompsonJ M₁ ⊔ T)) T →
        ¬ P ≤ (M₁ ⊓ Subgroup.centralizer (VZ T M₁ : Set G)) ⊔ T →
        IsSylowTwoOf (baum T) (oTwoUpper P ⊔ baum T)

end CFSG.Quasithin
