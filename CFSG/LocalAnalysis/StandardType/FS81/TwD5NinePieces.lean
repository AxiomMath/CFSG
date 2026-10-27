module

public import CFSG.LocalAnalysis.StandardType.FS81.TwD5Pieces
public import CFSG.Open.GLADefs
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.StandardType.FrameRoute.FS81

open CFSG.Open CFSG.Assembly CFSG.SignalizerFunctorTheorem

@[expose] def nineJ {G : Type} [Group G] (K : Subgroup G) (b : G) : Subgroup G :=
  ⁅K ⊓ Subgroup.centralizer ({b} : Set G), K ⊓ Subgroup.centralizer ({b} : Set G)⁆

@[expose] def T5Nine92 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (b₀ : G) (K E : Subgroup G), StdTwD5 b₀ K E →
    KProper InCatalog G → IsCharTwoType G →
    ∀ B : Basis3 G (5 + 1), Adapted B b₀ K E → RecOutTwD5 B b₀ → Fus42 B b₀ →
    Odd (Nat.card ↥(Subgroup.centralizer (E : Set G))) →
    ∀ t : G, orderOf t = 2 → t * B.b 0 * t⁻¹ = (B.b 0)⁻¹ → t * B.b 1 * t⁻¹ = (B.b 1)⁻¹ →
      (∀ j : Fin (5 + 1), 2 ≤ j.val → t * B.b j = B.b j * t) →
      Subgroup.centralizer ({t} : Set G) ⊓ Subgroup.centralizer ({B.b 2} : Set G) ≤
        GLAPPrimeCoreOf 3 (Subgroup.centralizer ({B.b 2} : Set G)) ⊔ Subgroup.zpowers b₀ ⊔
          Subgroup.zpowers (B.b 2) ⊔ nineJ K (B.b 2) ⊔ Subgroup.zpowers t

@[expose] def T5TwoLocalK : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (K : Subgroup G), IsTwD5 K → Subgroup.center K = ⊥ →
    ∀ T A : Subgroup G, T ≤ K → A ≤ K → T ≠ ⊥ → IsPGroup 2 T → IsElemAbelian 3 A →
      A ≤ Subgroup.normalizer (T : Set G) → Nat.card A ≤ 3 ^ 4

@[expose] def T5NineModel : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (b₀ : G) (K E : Subgroup G), StdTwD5 b₀ K E →
    ∀ B : Basis3 G (5 + 1), Adapted B b₀ K E → RecOutTwD5 B b₀ →
    ∀ t : G, orderOf t = 2 → t ∈ Subgroup.normalizer (K : Set G) →
      t * B.b 1 * t⁻¹ = (B.b 1)⁻¹ → (∀ j : Fin (5 + 1), 2 ≤ j.val → t * B.b j = B.b j * t) →
      IsSimpleGroup ↥(nineJ K (B.b 2)) ∧
        IsSimpleGroup ↥(nineJ K (B.b 2) ⊓ Subgroup.centralizer ({t} : Set G)) ∧
        6 ∣ Nat.card ↥(nineJ K (B.b 2) ⊓ Subgroup.centralizer ({t} : Set G)) ∧
        nineJ K (B.b 2) ⊓ Subgroup.centralizer
          ((nineJ K (B.b 2) ⊓ Subgroup.centralizer ({t} : Set G) : Subgroup G) : Set G) = ⊥

end CFSG.StandardType.FrameRoute.FS81

end
