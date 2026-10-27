module

public import CFSG.RankThree.GF2n.Stroth80.Sec715LayerConfigStmt

public section

namespace CFSG.RankThree.GF2n.Stroth80.S715L

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped Matrix


@[expose] def Sec715IrrConfigAStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) [(Q.subgroupOf M).Normal]
    (hc : Ctx M Q Z B) (n : ℕ) (t r : G) (hs : Sec7Hyp hc n t), Sec7A hc t r →
    OmegaPlusNat hc t 4 → n = 16 →
    ∀ Z0 : Subgroup G, IsCentrePre Z0 (Rt M (LB M Q B) t) Q → IsCentrePre Z0 (hc.CN t) Q →
    ∀ (K : Type) [Field K] [Finite K] (γ : G → K) (M₀ : Tim79.QuadModel Q Z K γ)
      (ρ : Mbar M Q →* Multiplicative (AddAut M₀.E)) (b : M₀.E) (hS : IsTensorSetup hc n M₀ ρ b)
      (φ₈ : ↥(bar M Q (Rt M (LB M Q B) t)) →* GL (Fin 4 ⊕ Fin 4) K),
      φ₈.range = StatedOmega (StatedQuadPlus 4 K) →
      (∀ x, φ₈ x = 1 ↔ (x : Mbar M Q) ∈ bar M Q (hc.CN t)) →
      ∀ e : ↥(hc.VtSub hS.model t) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K),
      (∀ (x : ↥(bar M Q (Rt M (LB M Q B) t))) (w : ↥(hc.VtSub hS.model t)),
        e ⟨(ρ (x : Mbar M Q)).toAdd w, hc.act_mem_VtSub hS hs.toSec5.mem _ x.2 _ w.2⟩ =
          (φ₈ x : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) K) *ᵥ e w) →
      (∀ g ∈ M, ∀ u ∈ Z0, u ∉ Q → g * u * g⁻¹ ∈ Z0 → g ∈ Subgroup.normalizer (Z0 : Set G)) →
      IsLayerConfigA hS hs.toSec5.mem →
      ∀ A : Subgroup G, Z0 ≤ A → A ≤ hc.CN t →
        (∀ k ∈ NormH0 M Z Z0, conjSubgroup k A = A) → A = Z0 ∨ A = hc.CN t

end CFSG.RankThree.GF2n.Stroth80.S715L
