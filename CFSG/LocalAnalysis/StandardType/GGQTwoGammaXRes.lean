module

public import CFSG.LocalAnalysis.StandardType.GGQTwoS5Defs
public import CFSG.LocalAnalysis.StandardType.GGQTwoPairsDefs

public section

namespace CFSG.StandardType

open Module

@[expose] def GGQ2XCovered {G : Type} [Group G] [Finite G] (p : ℕ) [Fact p.Prime]
    (B Bs : Subgroup G) (x : G) (L D J : Subgroup G) : Prop :=
  ∃ (y : G) (K : Subgroup G), GGNbr p B x D J y K ∧ ∃ M : GGQTwoModel p Bs x y D L J K,
    ((M.cartan.submatrix (fun i : {k // k ≠ M.a} => (i : M.ι))
      (fun i : {k // k ≠ M.a} => (i : M.ι))).det : ZMod p) ≠ 0 ∧
    Submodule.span (ZMod p) (insert M.xV (Set.range fun i : {k // k ≠ M.a} => M.coroot i)) = ⊤

@[expose] def GGQ2GammaXGraphInput : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G},
    GGQTwoSetting p B Bs x L D J → p = 3 → GGQTwoI1 Bs D J → x ∉ L → ∀ [Fact p.Prime]
    {y : G} {K : Subgroup G}, GGNbr p B x D J y K →
    ∀ M : GGQTwoModel p Bs x y D L J K,
      (∃ k : ℕ, 2 ≤ k ∧ ∃ f : Fin (2 * k) ≃ {i // i ≠ M.a},
        ∀ i j, M.cartan (f i) (f j) = CartanMatrix.D (2 * k) i j) →
      Submodule.span (ZMod p) (insert M.xV (Set.range fun i : {k // k ≠ M.a} => M.coroot i)) = ⊤ →
      ∀ φ ∈ ggAutomizer ⊤ Bs,
        ggLin (p := p) M.model φ M.xV ∈ Submodule.span (ZMod p) {M.xV} →
      ∀ (π : {k // k ≠ M.a} ≃ {k // k ≠ M.a}) (μ : {k // k ≠ M.a} → ZMod p) (c : ZMod p)
        (w : M.V ≃ₗ[ZMod p] M.V),
        M.toLin.ScaledAut M.a π μ → w ∈ M.toLin.parab {k | k ≠ M.a} →
        (∀ i : {k // k ≠ M.a},
          ggLin (p := p) M.model φ (M.coroot i) = c • μ i • w (M.coroot (π i))) →
        π ⟨M.b, M.a_ne_b.symm⟩ ≠ ⟨M.b, M.a_ne_b.symm⟩ → ¬ M.toLin.ScalarModW M.a π μ →
        φ ∈ ggAutomizer (Subgroup.normalizer (ggG0 p B x L D J : Set G)) Bs

@[expose] def GGQ2GammaXPosInput : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G},
    GGQTwoSetting p B Bs x L D J → p = 3 → GGQTwoI1 Bs D J → x ∉ L → ∀ [Fact p.Prime],
    (¬ ∃ (y : G) (K : Subgroup G), GGNbr p B x D J y K ∧
      ((GGQTwoTwoNodeRowAt p L J ∧ x ∉ L) ∨ (GGQTwoTwoNodeRowAt p K J ∧ y ∉ K))) →
    ¬ GGQ2XCovered p B Bs x L D J →
    ∀ {u : ↥Bs}, Subgroup.zpowers (u : G) = Subgroup.zpowers x → GGGammaAt p B Bs x L D J u

end CFSG.StandardType

end
