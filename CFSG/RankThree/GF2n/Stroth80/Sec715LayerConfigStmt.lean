module

public import CFSG.RankThree.GF2n.Stroth80.Sec715LayerConfig
public import CFSG.RankThree.GF2n.Stroth80.Sec715LayerForms
public import CFSG.RankThree.GF2n.Stroth80.Sec715LayerPair

public section

namespace CFSG.RankThree.GF2n.Stroth80.S715L

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
  [(Q.subgroupOf M).Normal] {hc : Ctx M Q Z B} {n : ℕ} {K : Type} [Field K] [Finite K]
  {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ} {ρ : Mbar M Q →* Multiplicative (AddAut M₀.E)}
  {b : M₀.E}

@[expose] def IsLayerConfigA (hS : IsTensorSetup hc n M₀ ρ b) {t : G} (ht : t ∈ LB M Q B) :
    Prop :=
  ∃ (L₃ L₄ : Type) (_ : AddCommGroup L₃) (_ : Module K L₃) (_ : AddCommGroup L₄)
    (_ : Module K L₄) (ρ₃ : ↥(bar M Q (Rt M (LB M Q B) t)) →* (L₃ ≃ₗ[K] L₃))
    (ρ₄ : ↥(bar M Q (Rt M (LB M Q B) t)) →* (L₄ ≃ₗ[K] L₄))
    (eM : wvQ hS t ≃ₗ[K] (Fin 2 → L₃)) (eN : ↥(deltaSub hS t) ≃ₗ[K] (Fin 2 → L₄))
    (μ : L₃ →ₗ[K] L₄ →ₗ[K] ↥(hc.VtSub hS.model t)) (q₃ : QuadraticForm K L₃)
    (q₄ : QuadraticForm K L₄) (φ ψ : Matrix (Fin 2) (Fin 2) K) (κ : K),
    Module.finrank K L₃ = 8 ∧ Module.finrank K L₄ = 8 ∧
    (∀ S : Submodule K L₃, (∀ x, ∀ a ∈ S, ρ₃ x a ∈ S) → S = ⊥ ∨ S = ⊤) ∧
    (∀ S : Submodule K L₄, (∀ x, ∀ c ∈ S, ρ₄ x c ∈ S) → S = ⊥ ∨ S = ⊤) ∧
    (∀ x m, eM (wvAct hS ht x m) = fun i => ρ₃ x (eM m i)) ∧
    (∀ x f, eN (deltaAct hS ht x f) = fun i => ρ₄ x (eN f i)) ∧
    (∀ (w : ↥(S714.wsub hS t)) (f : ↥(deltaSub hS t)),
      (f : ↥(S714.wsub hS t) →ₗ[K] M₀.E) w =
        ((∑ i, μ (eM (Submodule.Quotient.mk w) i) (eN f i) : ↥(hc.VtSub hS.model t)) :
          M₀.E)) ∧
    (∀ x a c, μ (ρ₃ x a) (ρ₄ x c) = vAct hS ht x (μ a c)) ∧ μ ≠ 0 ∧
    (∀ x a, q₃ (ρ₃ x a) = q₃ a) ∧ (∀ a, (∀ a', QuadraticMap.polar q₃ a a' = 0) → a = 0) ∧
    (∀ x c, q₄ (ρ₄ x c) = q₄ c) ∧ (∀ c, (∀ c', QuadraticMap.polar q₄ c c' = 0) → c = 0) ∧
    φ.transpose = φ ∧ φ * ψ = 1 ∧
    (∀ w w' : ↥(S714.wsub hS t), M₀.B (w : M₀.E) (w' : M₀.E) =
      ∑ i, ∑ j, φ i j * QuadraticMap.polar q₃ (eM (Submodule.Quotient.mk w) i)
        (eM (Submodule.Quotient.mk w') j)) ∧
    κ ≠ 0 ∧ ∀ f f' : ↥(deltaSub hS t),
      bN hS ht (f : ↥(S714.wsub hS t) →ₗ[K] M₀.E) (f' : ↥(S714.wsub hS t) →ₗ[K] M₀.E) =
        κ * ∑ i, ∑ j, ψ i j * QuadraticMap.polar q₄ (eN f i) (eN f' j)

@[expose] def Sec715LayerConfigStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) [(Q.subgroupOf M).Normal]
    (hc : Ctx M Q Z B) (n : ℕ) (t : G) (hs : Sec7Hyp hc n t), OmegaPlusNat hc t 4 → n = 16 →
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
      IsLayerConfigA hS hs.toSec5.mem ∨ IsLayerConfigC hS hs.toSec5.mem

end CFSG.RankThree.GF2n.Stroth80.S715L
