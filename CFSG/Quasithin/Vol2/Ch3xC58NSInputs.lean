module

public import CFSG.Quasithin.Background.C1GNBlocks
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellNatActual
public import CFSG.LocalAnalysis.QuasithinUnique.PushingUp.C5Rank1

public section

namespace CFSG.Quasithin.C58NS

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

@[expose] def EmbedLocal : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G → (∃ a b : G, a * b ≠ b * a) →
    quasithinIsQTKECat G →
    ∀ (T K₁ N₁ : Subgroup G) (t x : G), quasithinIsSylowTwo T →
      IsShort2 K₁ → ((∃ n : ℕ, 1 < n ∧ IsLin2Type K₁ n) ∨ IsAltType K₁ 5) →
      t ∈ T → t ∉ Subgroup.normalizer (K₁ : Set G) →
      (T ⊓ Subgroup.normalizer (K₁ : Set G)).relIndex T = 2 →
      (∀ a ∈ K₁, ∀ b ∈ conjSubgroup K₁ t, a * b = b * a) →
      IsSylowTwoOf (T ⊓ K₁) K₁ → CharTwo (K₁ ⊔ (T ⊓ Subgroup.normalizer (K₁ : Set G))) →
      (∃ M : Subgroup G, MinParabolic (K₁ ⊔ (T ⊓ Subgroup.normalizer (K₁ : Set G)))
        (T ⊓ Subgroup.normalizer (K₁ : Set G)) M) →
      C5.NoCommonNormal (T ⊓ Subgroup.normalizer (K₁ : Set G))
        (K₁ ⊔ (T ⊓ Subgroup.normalizer (K₁ : Set G)))
        (Subgroup.normalizer ((T ⊓ Subgroup.normalizer (K₁ : Set G) : Subgroup G) : Set G)) →
      x ∈ Subgroup.normalizer ((T ⊓ Subgroup.normalizer (K₁ : Set G) : Subgroup G) : Set G) →
      ¬ conjSubgroup (blockU K₁) x ≤ Subgroup.centralizer (blockU K₁ : Set G) →
      N₁ ≤ Subgroup.normalizer ((T ⊓ Subgroup.normalizer (K₁ : Set G) : Subgroup G) : Set G) →
      T ⊓ Subgroup.normalizer (K₁ : Set G) ≤ N₁ →
      N₁.relIndex
        (Subgroup.normalizer ((T ⊓ Subgroup.normalizer (K₁ : Set G) : Subgroup G) : Set G)) = 2 →
      IsSylowTwoOf (T ⊓ Subgroup.normalizer (K₁ : Set G)) N₁ →
      IsElemAbelian 2 (conjClosure (blockU K₁) N₁) →
      conjClosure (blockU K₁) N₁ ≤
        baum (T ⊓ Subgroup.normalizer (K₁ : Set G)) ⊓ Subgroup.centralizer (blockU K₁ : Set G) →
      N₁ ⊔ K₁ ≤ Subgroup.normalizer (conjClosure (blockU K₁) N₁ : Set G) →
      CharTwo (N₁ ⊔ K₁) → IsSylowTwoOf (T ⊓ Subgroup.normalizer (K₁ : Set G)) (N₁ ⊔ K₁) →
      (N₁ ⊔ K₁) ⊓
          Subgroup.normalizer ((T ⊓ Subgroup.normalizer (K₁ : Set G) : Subgroup G) : Set G) ≤
        Subgroup.normalizer (blockU K₁ : Set G)

@[expose] def MinParabolicBlockSubnormal : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (H T N R P L : Subgroup G),
    MinParabolic H T N → CharTwo H → IsSQTKTC H → ¬ Group.IsSolvable H →
    R ≤ T → T ≤ Subgroup.normalizer (R : Set G) → IsSylowTwoOf R (oTwoUpper H ⊔ R) →
    P ≤ oTwoUpper H ⊔ R → R ≤ P → ¬ P ≤ N → MinParabolic P R (P ⊓ N) →
    Setup.Campbell.NoCharNormal R H →
    IsChi0Block P L → ⁅L, thompsonJ R⁆ = L → P = R ⊔ conjClosure L R →
    IsBlock2 H L

end CFSG.Quasithin.C58NS
