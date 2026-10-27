module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Quasithin.Background.E2Hyp
public import CFSG.Quasithin.Background.E2Two

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique B6

namespace E2

namespace TI2b

@[expose] def Dich {G : Type} [Group G] (R Y : Subgroup G) : Prop :=
  R ≤ pCoreOf 2 Y ∨ R ⊓ (CFSG.solvableRadical ↥Y).map Y.subtype = ⊥

@[expose] def StarDich {G : Type} [Group G] (K Ts R₀ : Subgroup G) : Prop :=
  ∀ x : G, conjSub x R₀ ≤ Ts → ∀ Y : Subgroup G, Y ≤ K →
    Ts ⊓ K ⊓ Subgroup.centralizer (conjSub x R₀ : Set G) ≤ Y → Dich (conjSub x R₀) Y

@[expose] def L3Leaf : Prop :=
  ∀ (A : Type) [Group A] [Finite A] (Ts Ms K Es : Subgroup A) [K.Normal] (n : ℕ), 2 ≤ n →
    IsSylowTwoOf Ts ⊤ → K ⊔ Ts = ⊤ → (∀ a : A, (∀ x ∈ K, a * x = x * a) → a = 1) →
    IsPSL 3 2 n ↥K →
    (∀ P : Subgroup A, IsMaxParabolic2 K P →
      K ⊓ Subgroup.normalizer ((Ts ⊓ K : Subgroup A) : Set A) ≤ P →
        ¬ Ts ≤ Subgroup.normalizer (P : Set A)) →
    Ms ⊓ K = K ⊓ Subgroup.normalizer ((Ts ⊓ K : Subgroup A) : Set A) → Ts ≤ Ms → Es ≤ Ts →
    (∀ x ∈ Es, x * x = 1) → Ts ≤ Subgroup.normalizer (Es : Set A) →
    Ms ≤ Subgroup.normalizer (Es : Set A) → Es ≠ ⊥ →
    Es ≤ K ∧ Nat.card Es = 2 ^ n ∧ StarDich K Ts Es

@[expose] def Sp4Leaf : Prop :=
  ∀ (A : Type) [Group A] [Finite A] (Ts Ms K Es : Subgroup A) [K.Normal] (n : ℕ), 2 ≤ n →
    Hyp28 (⊤ : Subgroup A) Ts Ms Es → kerIn Ms ⊤ = ⊥ →
    Subgroup.centralizer (K : Set A) = ⊥ → K ⊔ Ts = ⊤ → IsSp4Prime n ↥K →
    Ms ⊓ K = K ⊓ Subgroup.normalizer ((Ts ⊓ K : Subgroup A) : Set A) →
    Ms ≤ Subgroup.normalizer (Es : Set A) →
    ∃ R₀ : Subgroup A, R₀ ≤ Es ∧ R₀ ≤ K ∧ Nat.card R₀ = 2 ^ n ∧ StarDich K Ts R₀

end TI2b

end E2

end CFSG.Quasithin
