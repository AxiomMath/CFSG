module

public import CFSG.Quasithin.Background.A3StructureDefs
public import CFSG.Quasithin.Background.G11Defs
public import CFSG.SignalizerFunctorTheorem.Quadratic.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.SignalizerFunctorTheorem.Quadratic CFSG.Quasithin.G11 CFSG.Open Subgroup
open scoped MatrixGroups

@[expose] def NatSumL2Input : Prop :=
  ∀ (n : ℕ), 1 < n → ∀ (H : Type) [Group H] [Finite H], CFSG.Quasithin.IsPSL 2 2 n H →
    ∀ (W : Type) [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
      (ρ : H →* LGL 2 W),
    (∃ D : Subgroup H, Nat.card D = 3 ∧ ∀ w : W, (∀ d ∈ D, ρ d w = w) → w = 0) →
    ∃ s : Finset (Submodule (ZMod 2) W),
      (∀ U ∈ s, ∀ h : H, ∀ u ∈ U, ρ h u ∈ U) ∧ s.sup id = ⊤ ∧
      (∀ U ∈ s, U ⊓ (s.erase U).sup id = ⊥) ∧
      ∀ U ∈ s, ∃ (K : Type) (_ : Field K) (_ : Finite K) (φ : H ≃* SL(2, K))
        (ψ : ↥U ≃+ (Fin 2 → K)),
        Nat.card K = 2 ^ n ∧ ∀ (h : H) (u : ↥U) (hu : ρ h (u : W) ∈ U),
          ψ ⟨ρ h (u : W), hu⟩ = (φ h : Matrix (Fin 2) (Fin 2) K).mulVec (ψ u)

@[expose] def SuzukiSubgroupInput : Prop :=
  ∀ (n : ℕ) (H : Type) [Group H] [Finite H], CFSG.Quasithin.IsSz n H →
    ∀ U : Subgroup H, U ≠ ⊤ → (∃ E : Subgroup H, E ≤ U ∧ IsElemAbelian 2 E ∧ Nat.card E = 4) →
      (∃ Q : Sylow 2 H, U ≤ normalizer ((Q : Subgroup H) : Set H)) ∨
      (∃ k : ℕ, k ∣ n ∧ k < n ∧ CFSG.Quasithin.IsSz k ↥U)

end CFSG.LocalAnalysis.WeakClosure81
