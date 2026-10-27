module

public import CFSG.Quasithin.Background.C2Blocks

public section

namespace CFSG.Quasithin.H13.Ch4

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin

@[expose] def KGHatA6M24He : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (K B S : Subgroup G),
    (IsSporadic .M24 ↥K ∨ IsSporadic .He ↥K) → B ≤ K → CFSG.Quasithin.IsHatA6Block B →
      IsSylowTwoOf S B →
      ∀ z ∈ blockU B ⊓ Subgroup.centralizer (S : Set G), orderOf z = 2 →
        ¬ blockU B ≤ pCoreOf 2 (K ⊓ Subgroup.centralizer ({z} : Set G))

@[expose] def KGG2BlockRu : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (K B S W : Subgroup G),
    ⁅K, K⁆ = K → IsSporadic .Ru (↥K ⧸ Subgroup.center ↥K) → B ≤ K →
      CFSG.Quasithin.IsG2Block B → IsSylowTwoOf S B → W ≤ blockU B →
      B ≤ Subgroup.normalizer (W : Set G) → Nat.card W = 2 ^ 6 →
        ∃ V₃ : Subgroup G, V₃ ≤ W ∧ Nat.card V₃ = 2 ^ 3 ∧ S ≤ Subgroup.normalizer (V₃ : Set G) ∧
          ¬ K ⊓ Subgroup.centralizer (V₃ : Set G) ≤ Subgroup.normalizer (B : Set G)

end CFSG.Quasithin.H13.Ch4
