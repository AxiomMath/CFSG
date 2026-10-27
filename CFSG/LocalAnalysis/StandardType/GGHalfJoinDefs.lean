module

public import CFSG.LocalAnalysis.StandardType.GGHalfFiveInputs

public section

namespace CFSG.StandardType

open CFSG.Assembly

@[expose] def GGHalfRowDataInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Bs K' : Subgroup G), GGInnerDiagOn Bs K' →
    (GGHasLabel ⟨.twD, 4, 1⟩ (↥K' ⧸ Subgroup.center ↥K') ∨
      GGHasLabel ⟨.E6, 0, 1⟩ (↥K' ⧸ Subgroup.center ↥K')) →
    Subgroup.center ↥K' = ⊥ ∧ ∀ b ∈ Bs, ∃ c ∈ K', ∀ l ∈ K', b * l * b⁻¹ = c * l * c⁻¹

@[expose] def GGHalfFusionAt (lab : LargeEvenLabel) (m : ℕ) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (K' J T : Subgroup G) (kx : G),
    CFSG.Assembly.IsQuasisimple ↥K' → Subgroup.center ↥K' = ⊥ →
    GGHasLabel lab (↥K' ⧸ Subgroup.center ↥K') → orderOf kx = 3 → kx ∈ K' →
    IsComponentOf J (K' ⊓ Subgroup.centralizer ({kx} : Set G)) → Subgroup.center ↥J = ⊥ →
    GGHasLabel ⟨.A, m, 1⟩ (↥J ⧸ Subgroup.center ↥J) → T ≤ J → IsElemAbelian 3 T →
    Nat.card T = 3 ^ ((m + 1) / 2) →
    ∃ n' ∈ K', n' ∈ Subgroup.normalizer ((Subgroup.zpowers kx ⊔ T : Subgroup G) : Set G) ∧
      n' * kx * n'⁻¹ ∈ T ∧ n' * kx * n'⁻¹ ≠ 1

@[expose] def GGHalfFusionOmega8Input : Prop := GGHalfFusionAt ⟨.twD, 4, 1⟩ 3

@[expose] def GGHalfFusionE6Input : Prop := GGHalfFusionAt ⟨.E6, 0, 1⟩ 5

end CFSG.StandardType

end
