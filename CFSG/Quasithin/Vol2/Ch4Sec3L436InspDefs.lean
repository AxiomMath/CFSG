module

public import CFSG.Quasithin.Vol2.Ch4Sec3L436

public section

namespace CFSG.Quasithin.H13.Ch4

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Assembly.LowTwoRank CFSG.Blueprint

@[expose] def Insp436G2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (K P V R₀ : Subgroup G) (n : ℕ), 2 ≤ n →
    CFSG.Open.IsQuasisimple ↥K → IsG2 2 n (↥K ⧸ Subgroup.center ↥K) → IsMaxParabolic2 K P →
    IsPSL 2 2 n (ModO2 (perfectCore P)) →
    (∃ (F : Type) (_ : Field F) (_ : Fintype F), Fintype.card F = 2 ^ n ∧
      IsNaturalSection (perfectCore P) V (V ⊓ centerOf K) (CFSG.pCore 2 ↥(perfectCore P))
        (CFSG.Assembly.LowTwoRank.StatedSL 2 F)) →
    V ≤ pCoreOf 2 (perfectCore P) ⊓ Subgroup.centralizer (pCoreOf 2 (perfectCore P) : Set G) →
    IsPGroup 2 ↥R₀ → R₀ ≤ Subgroup.normalizer (K : Set G) →
    R₀ ≤ Subgroup.centralizer (perfectCore P : Set G) →
    K ⊓ Subgroup.normalizer (R₀ : Set G) ≤ P → R₀ ≤ Subgroup.centralizer (K : Set G)

@[expose] def Insp436D4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (K P V R₀ : Subgroup G) (n : ℕ), 2 ≤ n →
    CFSG.Open.IsQuasisimple ↥K → Is3D4 2 n (↥K ⧸ Subgroup.center ↥K) → IsMaxParabolic2 K P →
    IsPSL 2 2 n (ModO2 (perfectCore P)) →
    (∃ (F : Type) (_ : Field F) (_ : Fintype F), Fintype.card F = 2 ^ n ∧
      IsNaturalSection (perfectCore P) V (V ⊓ centerOf K) (CFSG.pCore 2 ↥(perfectCore P))
        (CFSG.Assembly.LowTwoRank.StatedSL 2 F)) →
    V ≤ pCoreOf 2 (perfectCore P) ⊓ Subgroup.centralizer (pCoreOf 2 (perfectCore P) : Set G) →
    IsPGroup 2 ↥R₀ → R₀ ≤ Subgroup.normalizer (K : Set G) →
    R₀ ≤ Subgroup.centralizer (perfectCore P : Set G) →
    K ⊓ Subgroup.normalizer (R₀ : Set G) ≤ P → R₀ ≤ Subgroup.centralizer (K : Set G)

@[expose] def Insp436F4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (K P V R₀ : Subgroup G) (n : ℕ), 2 ≤ n →
    CFSG.Open.IsQuasisimple ↥K → Is2F4 n (↥K ⧸ Subgroup.center ↥K) → IsMaxParabolic2 K P →
    IsPSL 2 2 n (ModO2 (perfectCore P)) →
    (∃ (F : Type) (_ : Field F) (_ : Fintype F), Fintype.card F = 2 ^ n ∧
      IsNaturalSection (perfectCore P) V (V ⊓ centerOf K) (CFSG.pCore 2 ↥(perfectCore P))
        (CFSG.Assembly.LowTwoRank.StatedSL 2 F)) →
    V ≤ pCoreOf 2 (perfectCore P) ⊓ Subgroup.centralizer (pCoreOf 2 (perfectCore P) : Set G) →
    IsPGroup 2 ↥R₀ → R₀ ≤ Subgroup.normalizer (K : Set G) →
    R₀ ≤ Subgroup.centralizer (perfectCore P : Set G) →
    K ⊓ Subgroup.normalizer (R₀ : Set G) ≤ P → R₀ ≤ Subgroup.centralizer (K : Set G)

@[expose] def Insp436M22M23 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (K M M₀ R₀ : Subgroup G),
    CFSG.Open.IsQuasisimple ↥K → M₀ ≤ K → (M₀.subgroupOf M).Normal →
    M ≤ Subgroup.normalizer (K : Set G) → C436Two M M₀ K → conjClosure M₀ M = M₀ →
    IsPGroup 2 ↥R₀ → R₀ ≤ Subgroup.normalizer (K : Set G) →
    R₀ ≤ Subgroup.centralizer (M₀ : Set G) →
    K ⊓ Subgroup.normalizer (R₀ : Set G) ≤ M → R₀ ≤ Subgroup.centralizer (K : Set G)

end CFSG.Quasithin.H13.Ch4
