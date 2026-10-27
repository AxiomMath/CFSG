module

public import CFSG.Quasithin.Background.TwoReduced
public import CFSG.LocalAnalysis.QuasithinUnique.Defs

public section

namespace CFSG.Quasithin.SBd9

open CFSG.Open CFSG.QuasithinUnique
open scoped commutatorElement

structure LieL3 {G : Type} [Group G] (L Q : Subgroup G) (q : ℕ) : Prop where
  center_le : centerOf L ≤ Q
  solv : ∀ X : Subgroup G, Q ≤ X → X ≤ L → Group.IsSolvable ↥X →
    X ≤ Subgroup.normalizer (Q : Set G)
  cent : L ⊓ Subgroup.centralizer (Q : Set G) ≤ Q
  exp : ∀ W : Subgroup G, W ≤ L ⊓ Subgroup.centralizer (Q : Set G) →
    L ⊓ Subgroup.normalizer (Q : Set G) ≤ Subgroup.normalizer (W : Set G) →
    ¬ W ≤ centerOf L → ∀ m : ℕ,
      (∀ b ∈ L ⊓ Subgroup.normalizer (Q : Set G), ∀ w ∈ W, ⁅b ^ m, w⁆ ∈ centerOf L) → q - 1 ∣ m
  card : ∀ W : Subgroup G, W ≤ L ⊓ Subgroup.centralizer (Q : Set G) → W ⊓ centerOf L = ⊥ →
    Nat.card ↥W ≤ q
  reg4 : q = 4 → ∀ y ∈ L ⊓ Subgroup.normalizer (Q : Set G), orderOf y = 3 →
    ∀ x ∈ L ⊓ Subgroup.centralizer (Q : Set G), x * y = y * x → x ∈ centerOf L
  inner : ∀ w : G, w ∈ Subgroup.normalizer (L : Set G) → w ∈ Subgroup.centralizer (Q : Set G) →
    ∃ x ∈ L, ∀ y ∈ L, w⁻¹ * y * w = x⁻¹ * y * x

end CFSG.Quasithin.SBd9
