module

public import CFSG.Quasithin.Vol2.Ch12Sec9Lemma4DIFacts
public import CFSG.Quasithin.Background.A4Defs

public section

namespace CFSG.Quasithin.H13.C1294

open CFSG.Open CFSG.Quasithin

@[expose] def FactF5 : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V], Module.finrank (ZMod 2) V = 4 →
    ∀ V₁ : Submodule (ZMod 2) V, Module.finrank (ZMod 2) V₁ = 1 →
      ∀ X : Submodule (ZMod 2) V, Module.finrank (ZMod 2) X = 3 → V₁ ≤ X →
        ¬ (∀ γ ∈ oTwoUpper (stabS V₁), ∀ v : V, v ∈ X ↔ γ v ∈ X)

@[expose] def F4Out {W : Type} [AddCommGroup W] [Module (ZMod 2) W] [Finite W] (q : W → ZMod 2)
    (B : LinearMap.BilinForm (ZMod 2) W) (Ω : Subgroup (W ≃ₗ[ZMod 2] W)) : Prop :=
  (∀ v w : W, v ≠ 0 → w ≠ 0 → q v = 0 → q w = 0 → ∃ γ ∈ Ω, γ v = w) ∧
  (∀ v : W, v ≠ 0 → q v = 0 → (stabS (Submodule.span (ZMod 2) {v})).relIndex Ω = 35) ∧
  (∀ S : Submodule (ZMod 2) W, Module.finrank (ZMod 2) S = 3 → (∀ s ∈ S, q s = 0) →
    (∀ γ ∈ orthogonalSubgroupOf q, (∀ v, v ∈ S ↔ γ v ∈ S) → γ ∈ Ω) ∧
      (stabS S).relIndex Ω = 15 ∧
      Nat.card (pCoreOf 2 (stabS S ⊓ Ω)) = 8 ∧
      ∀ γ ∈ stabS S ⊓ Ω, (∀ s ∈ S, γ s = s) ↔ γ ∈ pCoreOf 2 (stabS S ⊓ Ω)) ∧
  (∀ w : W, w ≠ 0 → q w = 0 →
    Nat.card (pCoreOf 2 (stabS (Submodule.span (ZMod 2) {w}) ⊓ Ω)) = 16 ∧
      ∀ γ ∈ stabS (Submodule.span (ZMod 2) {w}) ⊓ Ω,
        (∀ x : W, B x w = 0 → γ x - x ∈ Submodule.span (ZMod 2) {w}) ↔
          γ ∈ pCoreOf 2 (stabS (Submodule.span (ZMod 2) {w}) ⊓ Ω))

end CFSG.Quasithin.H13.C1294
