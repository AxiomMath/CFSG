module

public import CFSG.RankThree.GF2n.Stroth80.Sec715LayerDefs

public section

namespace CFSG.RankThree.GF2n.Stroth80.S715L

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

section Generic

variable {K X H : Type*} [Field K] [AddCommGroup X] [Module K X] [Group H]

@[expose] def IsInvSub (act : H →* (X ≃ₗ[K] X)) (U : Submodule K X) : Prop :=
  ∀ h : H, ∀ x ∈ U, act h x ∈ U

@[expose] def IsIrrSub (act : H →* (X ≃ₗ[K] X)) (U : Submodule K X) : Prop :=
  U ≠ ⊥ ∧ IsInvSub act U ∧ ∀ U' : Submodule K X, U' ≤ U → IsInvSub act U' → U' = ⊥ ∨ U' = U

end Generic

section Root

variable {K : Type} [Field K]

@[expose] def IsTSLine8 (u w : Fin 4 ⊕ Fin 4 → K) : Prop :=
  LinearIndependent K ![u, w] ∧ StatedQuadPlus 4 K u = 0 ∧ StatedQuadPlus 4 K w = 0 ∧
    StatedQuadPlus 4 K (u + w) = 0

@[expose] def IsLongRoot8 (u w : Fin 4 ⊕ Fin 4 → K) (g : GL (Fin 4 ⊕ Fin 4) K) : Prop :=
  (∀ v, (g : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) K) *ᵥ v - v ∈ Submodule.span K {u, w}) ∧
  (∀ v, StatedQuadPlus 4 K (v + u) - StatedQuadPlus 4 K v - StatedQuadPlus 4 K u = 0 →
    StatedQuadPlus 4 K (v + w) - StatedQuadPlus 4 K v - StatedQuadPlus 4 K w = 0 →
    (g : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) K) *ᵥ v = v)

variable {X H : Type*} [AddCommGroup X] [Module K X] [Group H]

@[expose] def RootShape (φ : H →* GL (Fin 4 ⊕ Fin 4) K) (act : H →* (X ≃ₗ[K] X))
    (Y : Submodule K X) : Prop :=
  ∀ u w : Fin 4 ⊕ Fin 4 → K, IsTSLine8 u w →
    (∀ r : H, IsLongRoot8 u w (φ r) → φ r ≠ 1 →
      Module.finrank K (Y.map ((act r : X →ₗ[K] X) - LinearMap.id)) = 2) ∧
    ∀ r r' : H, IsLongRoot8 u w (φ r) → IsLongRoot8 u w (φ r') →
      ∀ κ : K, ((φ r' : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) K) - 1) =
          κ • ((φ r : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) K) - 1) →
        ∀ y ∈ Y, act r' y - y = κ • (act r y - y)

@[expose] def IsLayerSplit (φ : H →* GL (Fin 4 ⊕ Fin 4) K) (act : H →* (X ≃ₗ[K] X)) : Prop :=
  ∃ Y₁ Y₂ : Submodule K X, IsCompl Y₁ Y₂ ∧ IsIrrSub act Y₁ ∧ IsIrrSub act Y₂ ∧
    Module.finrank K Y₁ = 8 ∧ Module.finrank K Y₂ = 8 ∧ RootShape φ act Y₁ ∧ RootShape φ act Y₂

end Root


@[expose] def Sec715LayerSplitStatement : Prop :=
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
      IsLayerSplit φ₈ (wvAct hS hs.toSec5.mem) ∧ IsLayerSplit φ₈ (deltaAct hS hs.toSec5.mem)

end CFSG.RankThree.GF2n.Stroth80.S715L
