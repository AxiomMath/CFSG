module

public import CFSG.Quasithin.Background.E3Defs
public import CFSG.Quasithin.H13.StatementsCh7
public import CFSG.Quasithin.Vol2.Ch1Xi

public section

namespace CFSG.Quasithin.H13.L827X

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.E3
open scoped commutatorElement

@[expose] def XiChiefLowerBound : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T X K U V X₁ W₀ W₁ : Subgroup G) (v : G),
    quasithinIsSylowTwo T → IsXi T X → CharTwo (X ⊔ T) →
    quasithinIsCComponent K (Subgroup.normalizer (U : Set G)) → X ≤ K →
    Subgroup.normalizer (K : Set G) ≤ Subgroup.normalizer (X : Set G) →
    (∀ K' : Subgroup G, K' ≤ K → ⁅K', X⁆ ≤ pCoreOf 2 X → Group.IsSolvable ↥K') →
    X ≤ Subgroup.centralizer (U : Set G) → T ≤ Subgroup.normalizer (U : Set G) →
    U ≤ V → V ≤ T → T ≤ Subgroup.normalizer (V : Set G) → (∀ x ∈ V, x ^ 2 = 1) →
    pCoreOf 2 X < X₁ → X₁ ≤ X → T ≤ Subgroup.normalizer (X₁ : Set G) →
    v ∈ V → ¬ ⁅X₁, Subgroup.zpowers v⁆ ≤ pCoreOf 2 X →
    U ≤ W₀ → W₀ < W₁ → W₁ ≤ pCoreOf 2 X ⊔ U →
    (CFSG.Quasithin.conjClosure K T ⊔ T) ≤ Subgroup.normalizer (W₀ : Set G) →
    (CFSG.Quasithin.conjClosure K T ⊔ T) ≤ Subgroup.normalizer (W₁ : Set G) →
    (∀ B : Subgroup G, W₀ ≤ B → B ≤ W₁ →
      (CFSG.Quasithin.conjClosure K T ⊔ T) ≤ Subgroup.normalizer (B : Set G) →
      B = W₀ ∨ B = W₁) →
    ¬ ⁅W₁, X₁⁆ ≤ W₀ →
    8 ≤ mQuot (⁅W₁, Subgroup.zpowers v⁆ ⊔ W₀) W₀

@[expose] def Stmt827VCard : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G) [IsMulCommutative ↥(fsuV T I)],
    Hyp7_0_2 G T L I → (Row711L3Nine T L I 1 ∨ Row711M22Code T L I) →
      Nat.card ↥(fsuV T I) ≤ 2 ^ 10

@[expose] def SL2OrbitFacts : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∀ (E : Type) [AddCommGroup E] [Module (ZMod p) E]
    [Finite E], Module.finrank (ZMod p) E = 2 → ∀ Λ : Subgroup (E ≃ₗ[ZMod p] E),
      Group.IsPerfect ↥Λ → ¬ Group.IsSolvable ↥Λ →
      5 ≤ p ∧
      (∀ x : E, x ≠ 0 → 24 ≤ Set.ncard {y : E | ∃ g ∈ Λ, g x = y}) ∧
      (∀ x : E, x ≠ 0 → ∀ ℓ : Submodule (ZMod p) E, Module.finrank (ZMod p) ℓ = 1 →
        3 * Set.ncard ({y : E | ∃ g ∈ Λ, g x = y} ∩ (ℓ : Set E)) ≤
          Set.ncard {y : E | ∃ g ∈ Λ, g x = y})

end CFSG.Quasithin.H13.L827X
