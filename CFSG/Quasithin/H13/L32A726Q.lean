module

public import CFSG.Quasithin.Background.C2Defs
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115List

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

@[expose] def KG14726C27C : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (H R M K : Subgroup G), HypC23 H R M → K ∈ cComp H →
    CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K) → CharTwo K → ¬ K ≤ M →
    R ≤ Subgroup.normalizer (K : Set G) →
    ∀ A : Subgroup (MulAut (↥K ⧸ CFSG.pCore 2 ↥K)),
      (MulAut.conj : (↥K ⧸ CFSG.pCore 2 ↥K) →* MulAut (↥K ⧸ CFSG.pCore 2 ↥K)).range ≤ A →
      ∀ B : Subgroup (MulAut (↥K ⧸ CFSG.pCore 2 ↥K)), B ≤ A → ¬ 2 ∣ (B.subgroupOf A).index →
        (∃ a : ℕ, Nat.card B = 2 ^ a * 27) →
        (∃ x ∈ (MulAut.conj : (↥K ⧸ CFSG.pCore 2 ↥K) →* MulAut (↥K ⧸ CFSG.pCore 2 ↥K)).range,
          orderOf x = 3 ∧ x ∈ B ∧
            B ≤ Subgroup.normalizer ((Subgroup.zpowers x ⊔ pCoreOf 2 B :
              Subgroup (MulAut (↥K ⧸ CFSG.pCore 2 ↥K))) : Set (MulAut (↥K ⧸ CFSG.pCore 2 ↥K)))) →
        (∀ k : ↥K, (k : G) ∈ M →
          MulAut.conj (QuotientGroup.mk k : ↥K ⧸ CFSG.pCore 2 ↥K) ∈ B) →
        ¬ IsPOnePlusTwo 3 ↥(oTwoUpper (⊤ : Subgroup (↥B ⧸ CFSG.pCore 2 ↥B)))

@[expose] def KG14726L115C : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (z : G), Lemma115Cases L z →
    CFSG.IsQuasisimple ↥L → 3 ∣ Nat.card L →
    ∀ A : Subgroup (MulAut ↥L), (MulAut.conj : ↥L →* MulAut ↥L).range ≤ A →
      ∀ B : Subgroup (MulAut ↥L), B ≤ A → ¬ 2 ∣ (B.subgroupOf A).index →
        (∃ a : ℕ, Nat.card B = 2 ^ a * 27) →
        (∃ x ∈ (MulAut.conj : ↥L →* MulAut ↥L).range, orderOf x = 3 ∧ x ∈ B ∧
          (IsPGroup 2 ↥(Subgroup.center ↥L) → ∃ N : Subgroup (MulAut ↥L),
            N ≤ (MulAut.conj : ↥L →* MulAut ↥L).range ∧ x ∈ N ∧
            B ≤ Subgroup.normalizer (N : Set (MulAut ↥L)) ∧
            ∀ a ∈ (MulAut.conj : ↥L →* MulAut ↥L).range,
              a ∈ Subgroup.normalizer (N : Set (MulAut ↥L)) → a ∈ B) ∧
          B ≤ Subgroup.normalizer ((Subgroup.zpowers x ⊔ pCoreOf 2 B : Subgroup (MulAut ↥L)) :
            Set (MulAut ↥L))) →
        (∃ ζ ∈ B, ζ ≠ 1 ∧ (∀ ℓ : ↥L, ((ζ ℓ : ↥L) : G) = z * ℓ * z⁻¹) ∧
          ∀ b ∈ B, b * ζ = ζ * b) →
        (∀ ℓ : ↥L, (ℓ : G) * z = z * ℓ → MulAut.conj ℓ ∈ B) →
        ¬ IsPOnePlusTwo 3 ↥(oTwoUpper (⊤ : Subgroup (↥B ⧸ CFSG.pCore 2 ↥B)))

end CFSG.Quasithin.H13
