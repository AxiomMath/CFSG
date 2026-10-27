module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Quasithin.Background.E3Defs
public import CFSG.Quasithin.Vol2.Ch1Xi
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.Quasithin.H13.L827X.LBDefs

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.E3
open scoped commutatorElement

variable {G : Type} [Group G]

@[expose] def XiY (X : Subgroup G) : Subgroup G := ⁅X, X⁆ ⊔ pCoreOf 2 X

@[expose] def XiHyp (T X K U V X₁ W₀ W₁ : Subgroup G) (v : G) : Prop :=
  quasithinIsSylowTwo T ∧ IsXi T X ∧ CharTwo (X ⊔ T) ∧
  quasithinIsCComponent K (Subgroup.normalizer (U : Set G)) ∧ X ≤ K ∧
  Subgroup.normalizer (K : Set G) ≤ Subgroup.normalizer (X : Set G) ∧
  (∀ K' : Subgroup G, K' ≤ K → ⁅K', X⁆ ≤ pCoreOf 2 X → Group.IsSolvable ↥K') ∧
  X ≤ Subgroup.centralizer (U : Set G) ∧ T ≤ Subgroup.normalizer (U : Set G) ∧
  U ≤ V ∧ V ≤ T ∧ T ≤ Subgroup.normalizer (V : Set G) ∧ (∀ x ∈ V, x ^ 2 = 1) ∧
  pCoreOf 2 X < X₁ ∧ X₁ ≤ X ∧ T ≤ Subgroup.normalizer (X₁ : Set G) ∧
  v ∈ V ∧ ¬ ⁅X₁, Subgroup.zpowers v⁆ ≤ pCoreOf 2 X ∧
  U ≤ W₀ ∧ W₀ < W₁ ∧ W₁ ≤ pCoreOf 2 X ⊔ U ∧
  (CFSG.Quasithin.conjClosure K T ⊔ T) ≤ Subgroup.normalizer (W₀ : Set G) ∧
  (CFSG.Quasithin.conjClosure K T ⊔ T) ≤ Subgroup.normalizer (W₁ : Set G) ∧
  (∀ B : Subgroup G, W₀ ≤ B → B ≤ W₁ →
    (CFSG.Quasithin.conjClosure K T ⊔ T) ≤ Subgroup.normalizer (B : Set G) → B = W₀ ∨ B = W₁) ∧
  ¬ ⁅W₁, X₁⁆ ≤ W₀

@[expose] def ChiefRepProps {W : Type} [AddCommGroup W] [Module (ZMod 2) W]
    (Λ O W₀ W₁ : Subgroup G) (τ : Λ →* (W ≃ₗ[ZMod 2] W)) (π : W₁ → W) : Prop :=
  Nontrivial W ∧ Function.Surjective π ∧ (∀ a b : W₁, π (a * b) = π a + π b) ∧
  (∀ w : W₁, π w = 0 ↔ (w : G) ∈ W₀) ∧
  (∀ (l : Λ) (w w' : W₁), (w' : G) = (l : G) * w * (l : G)⁻¹ → τ l (π w) = π w') ∧
  (∀ o : Λ, (o : G) ∈ O → τ o = 1) ∧
  (∀ S : Submodule (ZMod 2) W, (∀ l : Λ, ∀ w ∈ S, τ l w ∈ S) → S = ⊥ ∨ S = ⊤)

end CFSG.Quasithin.H13.L827X.LBDefs
