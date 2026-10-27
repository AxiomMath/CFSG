module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveOrthD4Excl

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Open CFSG.Blueprint

@[expose] def GGSecFiveOrthD4KStructInput
    : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (𝒦 : Finset (Subgroup G)), GGSecFiveRouteCfg' p B Bs x L D J 𝒦 → GGSplitLie p L →
      (∀ b : ↥Bs, (∀ φ ∈ ggAInf p B Bs x L D J, φ b = b) → b = 1) → p = 3 →
        ∀ (V : Type) [AddCommGroup V] [Module (ZMod p) V] (Q : QuadraticForm (ZMod p) V),
          (QuadraticMap.polarBilin Q).Nondegenerate → ∀ [Fact p.Prime] (ι : Additive ↥Bs ≃+ V),
          Module.finrank (ZMod p) V = 5 →
          (∀ g : V ≃ₗ[ZMod p] V, (∃ a ∈ ggAInf p B Bs x L D J, ggLin (p := p) ι a = g) ↔
            ∀ v, Q (g v) = Q v) →
          GGWeylOfType p (ggCoxeterMatrixD 4) (ggAutomizer L Bs) →
          ∀ (y : G) (K : Subgroup G), GGNbr p B x D J y K →
            (∃ m : ℕ, 8 ≤ m ∧ Nonempty (↥K ≃* ↥(StatedSL m (ZMod 2)))) →
            CFSG.Assembly.IsComponentOf J (Subgroup.centralizer ({x} : Set G) ⊓ K) →
            (∃ f : ℕ, 2 ≤ f ∧ StatedClassicalModel (↥J ⧸ Subgroup.center ↥J) .PSL 4 2 f) →
            GGWeylOfType p (CoxeterMatrix.B 4) (ggAutomizer K Bs) ∧
              (∀ b : ↥Bs, (∀ φ ∈ ggAutomizer K Bs, φ b = b) → (b : G) ∈ Subgroup.zpowers y) ∧
              (∀ φ : ↥(ggAutomizer K Bs), GGIsReflection p (φ : MulAut ↥Bs) →
                Nat.card {ψ : ↥(ggAutomizer K Bs) // IsConj φ ψ} = 4 →
                ∀ hx : x ∈ Bs, (φ : MulAut ↥Bs) ⟨x, hx⟩ ≠ ⟨x, hx⟩)

end CFSG.StandardType

end
