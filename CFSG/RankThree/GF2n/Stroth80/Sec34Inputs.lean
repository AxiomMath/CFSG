module

public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.Open

@[expose] def HKSStatement : Prop :=
  ∀ (H : Type) [Group H] [Finite H] (Ω : Type) [Finite Ω] [MulAction H Ω] [FaithfulSMul H Ω]
    (m : ℕ), 2 ≤ m → Nat.card Ω = 2 ^ m + 1 → MulAction.IsMultiplyPretransitive H Ω 2 →
    ∀ (α : Ω) (R : Subgroup H), R ≤ MulAction.stabilizer H α →
      (R.subgroupOf (MulAction.stabilizer H α)).Normal → IsElemAbelian 2 R →
      (∀ β γ : Ω, β ≠ α → γ ≠ α → ∃! r : R, (r : H) • β = γ) →
      ∃ L : Subgroup H, L.Normal ∧ IsSimpleGroup L ∧
        Nonempty (L ≃* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 m)) ∧
        MulAction.IsMultiplyPretransitive L Ω 2

@[expose] def SL2ModuleDimStatement : Prop :=
  ∀ (k : ℕ), 2 ≤ k → ∀ (V : Type) [AddCommGroup V] [Module (GaloisField 2 k) V]
    [Module.Finite (GaloisField 2 k) V] [Nontrivial V]
    (ρ : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 (2 * k)) →*
      (V ≃ₗ[GaloisField 2 k] V)),
    (∀ W : Submodule (GaloisField 2 k) V, (∀ g, ∀ v ∈ W, ρ g v ∈ W) → W = ⊥ ∨ W = ⊤) →
    (∃ g, ρ g ≠ 1) →
    ∃ j : ℕ, 2 ≤ j ∧ Module.finrank (GaloisField 2 k) V = 2 ^ j

end CFSG.RankThree.GF2n.Stroth80
