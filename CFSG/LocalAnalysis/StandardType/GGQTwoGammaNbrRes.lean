module

public import CFSG.LocalAnalysis.StandardType.GGQTwoS5Defs
public import CFSG.LocalAnalysis.StandardType.GGQTwoPairsDefs

public section

namespace CFSG.StandardType

open Module

@[expose] def GGQ2GammaNbrGraphInput : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G},
    GGQTwoSetting p B Bs x L D J → p = 3 → GGQTwoI1 Bs D J → x ∉ L → ∀ [Fact p.Prime]
    {y : G} {K : Subgroup G}, GGNbr p B x D J y K →
    ∀ M : GGQTwoModel p Bs x y D L J K,
      (∃ k : ℕ, 2 ≤ k ∧ ∃ f : Fin (2 * k) ≃ {i // i ≠ M.b},
        ∀ i j, M.cartan (f i) (f j) = CartanMatrix.D (2 * k) i j) →
      Submodule.span (ZMod p) (insert M.yV (Set.range fun i : {k // k ≠ M.b} => M.coroot i)) = ⊤ →
      ∀ φ ∈ ggAutomizer ⊤ Bs,
        ggLin (p := p) M.model φ M.yV ∈ Submodule.span (ZMod p) {M.yV} →
      ∀ (π : {k // k ≠ M.b} ≃ {k // k ≠ M.b}) (μ : {k // k ≠ M.b} → ZMod p) (c : ZMod p)
        (w : M.V ≃ₗ[ZMod p] M.V),
        M.toLin.ScaledAut M.b π μ → w ∈ M.toLin.parab {k | k ≠ M.b} →
        (∀ i : {k // k ≠ M.b},
          ggLin (p := p) M.model φ (M.coroot i) = c • μ i • w (M.coroot (π i))) →
        π ⟨M.a, M.a_ne_b⟩ ≠ ⟨M.a, M.a_ne_b⟩ →
        ¬ M.toLin.ScalarModW M.b π μ →
        φ ∈ ggAutomizer (Subgroup.normalizer (ggG0 p B x L D J : Set G)) Bs

@[expose] def GGQ2GammaNbrDetInput : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G},
    GGQTwoSetting p B Bs x L D J → p = 3 → GGQTwoI1 Bs D J → x ∉ L → ∀ [Fact p.Prime]
    {y : G} {K : Subgroup G}, GGNbr p B x D J y K →
    ¬ (GGQTwoTwoNodeRowAt p L J ∨ GGQTwoTwoNodeRowAt p K J) →
    ∀ M : GGQTwoModel p Bs x y D L J K, (∃! c, c ≠ M.b ∧ M.cartan M.b c ≠ 0) →
      ((M.cartan.submatrix (fun i : {k // k ≠ M.b} => (i : M.ι))
        (fun i : {k // k ≠ M.b} => (i : M.ι))).det : ZMod p) = 0 →
      ∀ {u : ↥Bs}, Subgroup.zpowers (u : G) = Subgroup.zpowers y → GGGammaAt p B Bs x L D J u

@[expose] def GGQ2GammaNbrPosInput : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G},
    GGQTwoSetting p B Bs x L D J → p = 3 → GGQTwoI1 Bs D J → x ∉ L → ∀ [Fact p.Prime]
    {y : G} {K : Subgroup G}, GGNbr p B x D J y K →
    ¬ (GGQTwoTwoNodeRowAt p L J ∨ GGQTwoTwoNodeRowAt p K J) →
    (∀ M : GGQTwoModel p Bs x y D L J K, ¬ ∃! c, c ≠ M.b ∧ M.cartan M.b c ≠ 0) →
    ∀ {u : ↥Bs}, Subgroup.zpowers (u : G) = Subgroup.zpowers y → GGGammaAt p B Bs x L D J u

end CFSG.StandardType

end
