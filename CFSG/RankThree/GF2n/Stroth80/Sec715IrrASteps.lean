module

public import CFSG.RankThree.GF2n.Stroth80.Sec715IrrAIface

public section

namespace CFSG.RankThree.GF2n.Stroth80.S715L

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped Matrix


@[expose] def Sec715HasLineStatement : Prop :=
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
      ∀ (L₃ L₄ : Type) [AddCommGroup L₃] [Module K L₃] [AddCommGroup L₄] [Module K L₄]
        (ρ₃ : ↥(bar M Q (Rt M (LB M Q B) t)) →* (L₃ ≃ₗ[K] L₃))
        (ρ₄ : ↥(bar M Q (Rt M (LB M Q B) t)) →* (L₄ ≃ₗ[K] L₄))
        (eM : wvQ hS t ≃ₗ[K] (Fin 2 → L₃)) (eN : ↥(deltaSub hS t) ≃ₗ[K] (Fin 2 → L₄))
        (μ : L₃ →ₗ[K] L₄ →ₗ[K] ↥(hc.VtSub hS.model t)) (q₃ : QuadraticForm K L₃)
        (q₄ : QuadraticForm K L₄) (φ ψ : Matrix (Fin 2) (Fin 2) K) (κ : K),
        ConfigAData hS hs.toSec5.mem ρ₃ ρ₄ eM eN μ q₃ q₄ φ ψ κ →
        HasLineProp hS t eN q₄ Z0

@[expose] def Sec715SameLineOrthStatement : Prop :=
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
      ∀ (L₃ L₄ : Type) [AddCommGroup L₃] [Module K L₃] [AddCommGroup L₄] [Module K L₄]
        (ρ₃ : ↥(bar M Q (Rt M (LB M Q B) t)) →* (L₃ ≃ₗ[K] L₃))
        (ρ₄ : ↥(bar M Q (Rt M (LB M Q B) t)) →* (L₄ ≃ₗ[K] L₄))
        (eM : wvQ hS t ≃ₗ[K] (Fin 2 → L₃)) (eN : ↥(deltaSub hS t) ≃ₗ[K] (Fin 2 → L₄))
        (μ : L₃ →ₗ[K] L₄ →ₗ[K] ↥(hc.VtSub hS.model t)) (q₃ : QuadraticForm K L₃)
        (q₄ : QuadraticForm K L₄) (φ ψ : Matrix (Fin 2) (Fin 2) K) (κ : K),
        ConfigAData hS hs.toSec5.mem ρ₃ ρ₄ eM eN μ q₃ q₄ φ ψ κ →
        SameLineOrthProp hS t eN Z0

@[expose] def Sec715RootEltStatement : Prop :=
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
      ∀ (L₃ L₄ : Type) [AddCommGroup L₃] [Module K L₃] [AddCommGroup L₄] [Module K L₄]
        (ρ₃ : ↥(bar M Q (Rt M (LB M Q B) t)) →* (L₃ ≃ₗ[K] L₃))
        (ρ₄ : ↥(bar M Q (Rt M (LB M Q B) t)) →* (L₄ ≃ₗ[K] L₄))
        (eM : wvQ hS t ≃ₗ[K] (Fin 2 → L₃)) (eN : ↥(deltaSub hS t) ≃ₗ[K] (Fin 2 → L₄))
        (μ : L₃ →ₗ[K] L₄ →ₗ[K] ↥(hc.VtSub hS.model t)) (q₃ : QuadraticForm K L₃)
        (q₄ : QuadraticForm K L₄) (φ ψ : Matrix (Fin 2) (Fin 2) K) (κ : K),
        ConfigAData hS hs.toSec5.mem ρ₃ ρ₄ eM eN μ q₃ q₄ φ ψ κ →
        RootEltProp hS t eN Z0

@[expose] def Sec715NonOrthNbrsStatement : Prop :=
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
      ∀ (L₃ L₄ : Type) [AddCommGroup L₃] [Module K L₃] [AddCommGroup L₄] [Module K L₄]
        (ρ₃ : ↥(bar M Q (Rt M (LB M Q B) t)) →* (L₃ ≃ₗ[K] L₃))
        (ρ₄ : ↥(bar M Q (Rt M (LB M Q B) t)) →* (L₄ ≃ₗ[K] L₄))
        (eM : wvQ hS t ≃ₗ[K] (Fin 2 → L₃)) (eN : ↥(deltaSub hS t) ≃ₗ[K] (Fin 2 → L₄))
        (μ : L₃ →ₗ[K] L₄ →ₗ[K] ↥(hc.VtSub hS.model t)) (q₃ : QuadraticForm K L₃)
        (q₄ : QuadraticForm K L₄) (φ ψ : Matrix (Fin 2) (Fin 2) K) (κ : K),
        ConfigAData hS hs.toSec5.mem ρ₃ ρ₄ eM eN μ q₃ q₄ φ ψ κ →
        NonOrthNbrsProp M₀ ρ hc t Z0

end CFSG.RankThree.GF2n.Stroth80.S715L
