module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC8HatDefs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefsB

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

structure C8KNat (Γ : Type) [Group Γ] [Finite Γ] (d : Γ)
    (ρ : Γ →* ↥(StatedSL 2 (ZMod 7))) (O Z : Subgroup Γ) : Prop where
  surj : Function.Surjective ρ
  ker_le : ρ.ker ≤ CFSG.pPrimeCore 3 Γ
  normal : O.Normal
  z_normal : Z.Normal
  q_le : CFSG.pCore 2 Γ ≤ Z
  z_le : Z ≤ O
  seven : ∀ x ∈ O, ∃ n : ℕ, x ^ 7 ^ n ∈ CFSG.pCore 2 Γ
  o_le_ker : O ≤ ρ.ker
  index : Z.relIndex O = 49
  comm : ∀ x ∈ O, ∀ y ∈ O, x * y * x⁻¹ * y⁻¹ ∈ Z
  pow : ∀ x ∈ O, x ^ 7 ∈ Z
  ngen : ∀ H : Subgroup Γ, H ≤ O → H ⊔ Z = O → H ⊔ CFSG.pCore 2 Γ = O
  cent : ∀ n ∈ ρ.ker, ¬ 7 ∣ orderOf n → ∀ x ∈ O, n * x * n⁻¹ * x⁻¹ ∈ CFSG.pCore 2 Γ
  act_one : ∀ γ : Γ, ρ γ = 1 ↔ ∀ x ∈ O, γ * x * γ⁻¹ * x⁻¹ ∈ Z
  inv : ∀ γ : Γ, ρ γ ≠ 1 → ρ γ ^ 2 = 1 → ∀ x ∈ O, γ * x * γ⁻¹ * x ∈ Z
  irred : ∀ W : Subgroup Γ, Z ≤ W → W ≤ O → (∀ γ : Γ, ∀ w ∈ W, γ * w * γ⁻¹ ∈ W) →
    W = Z ∨ W = O

@[expose] def C8P0 {Γ : Type} [Group Γ] (B C₀ : Subgroup Γ) : Prop :=
  ∃ (P : Type) (_ : Group P) (φ : ↥B →* P), Function.Surjective φ ∧
    φ.ker = C₀.subgroupOf B ∧ IsE64L3 P ∧ Group.IsPerfect P

structure C8KConf (Γ : Type) [Group Γ] [Finite Γ] (B S C₀ : Subgroup Γ) (d : Γ) : Prop where
  ctx : C8KCtx Γ B d
  sylow : IsSylowIn 2 S ⊤
  s_le : S ≤ B
  char2 : centralizer (CFSG.pCore 2 Γ : Set Γ) ≤ CFSG.pCore 2 Γ
  c0_le : C₀ ≤ B
  p0 : C8P0 B C₀
  c0_cent : ∀ R : Subgroup Γ, R ≤ C₀ → IsPGroup 7 R → (∀ x ∈ R, d * x * d⁻¹ ∈ R) →
    ∀ x ∈ R, d * x = x * d
  minimal : ∀ O : Subgroup Γ, O.Normal → ¬ O ≤ B →
    ∃ Y : Subgroup Γ, Y ≤ B ∧ Y ⊔ O = ⊤ ∧ ∀ y ∈ Y, y ∈ C₀ → Odd (orderOf y) → y = 1

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
