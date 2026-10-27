module

public import CFSG.RankThree.PartTwo.Sec21.FF84S4Inputs
public import CFSG.RankThree.PartTwo.Sec21.FF84S4OmIso
public import CFSG.RankThree.PartTwo.Sec21.FF84S4OmNonsing

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF84.S4

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

open CFSG CFSG.RankThree.PartTwo.Sec21 CFSG.RankThree.PartTwo.Sec21.FF84
open CFSG.ComponentClassification.AS81 CFSG.ComponentClassification.AS81.Sec2Omega
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)

variable {G : Type} [Group G]

open scoped _root_.Classical in
@[expose] noncomputable def ncomp (S : Subgroup G) (b b₁ b₂ : G) (x : G) : ℕ :=
  (if x ∈ ⁅S, Subgroup.zpowers b₁⁆ ⊔ ⁅S, Subgroup.zpowers b₂⁆ then 0 else 1) +
    (if x ∈ ⁅S, Subgroup.zpowers b⁆ ⊔ ⁅S, Subgroup.zpowers b₂⁆ then 0 else 1) +
    (if x ∈ ⁅S, Subgroup.zpowers b⁆ ⊔ ⁅S, Subgroup.zpowers b₁⁆ then 0 else 1)

@[expose] def FF84OmegaData (S : Subgroup G) : Prop :=
  ∃ (e : ↥S ≃* Multiplicative F6) (ψ : ↥(Nor S) →* OmG), Function.Surjective ψ ∧
    ψ.ker = S.subgroupOf (Nor S) ∧
    (∀ (n : G) (hn : n ∈ Nor S) (x : ↥S), ∃ hx : n * (x : G) * n⁻¹ ∈ S,
      e ⟨n * (x : G) * n⁻¹, hx⟩ =
        Multiplicative.ofAdd ((ψ ⟨n, hn⟩ : F6 ≃ₗ[ZMod 2] F6) (Multiplicative.toAdd (e x)))) ∧
    ∀ x : ↥S, (x : G) ≠ 1 → (qMinus (Multiplicative.toAdd (e x)) = 1 ↔ Op 2 (Cen (x : G)) = S)

@[expose] def FF84OmegaDataFor (S : Subgroup G) (e : ↥S ≃* Multiplicative F6) : Prop :=
  ∃ ψ : ↥(Nor S) →* OmG, Function.Surjective ψ ∧
    ψ.ker = S.subgroupOf (Nor S) ∧
    (∀ (n : G) (hn : n ∈ Nor S) (x : ↥S), ∃ hx : n * (x : G) * n⁻¹ ∈ S,
      e ⟨n * (x : G) * n⁻¹, hx⟩ =
        Multiplicative.ofAdd ((ψ ⟨n, hn⟩ : F6 ≃ₗ[ZMod 2] F6) (Multiplicative.toAdd (e x)))) ∧
    ∀ x : ↥S, (x : G) ≠ 1 → (qMinus (Multiplicative.toAdd (e x)) = 1 ↔ Op 2 (Cen (x : G)) = S)

@[expose] def HypS48CSb : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (b : G) (L B K : Subgroup G) (b₁ b₂ : G),
    FF84Post b L B K b₁ b₂ → ∀ U ∈ PiStar (Cen b) B 2, Op 2 (Nor U) ⊓ Cen b = U

@[expose] def HypS48b2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (b : G) (L B K : Subgroup G) (b₁ b₂ : G),
    FF84Post b L B K b₁ b₂ → ∀ U ∈ PiStar (Cen b) B 2,
      Nat.card ↥(Op 2 (Nor U) ⊓ Cen b₂) = 16 ∧ Nat.card ↥(Op 2 (Nor U) ⊓ Cen b₁) = 16 ∧
        Op 2 (Nor U) ⊓ CenS B = ⊥

@[expose] def HypS49orbits : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (b : G) (L B K : Subgroup G) (b₁ b₂ : G),
    FF84Post b L B K b₁ b₂ → ∀ U ∈ PiStar (Cen b) B 2,
      ∃ Δ₁ Δ₂ : Set G, Δ₁ ∪ Δ₂ = (Op 2 (Nor U) : Set G) \ {1} ∧ Disjoint Δ₁ Δ₂ ∧
        Δ₁.ncard = 36 ∧ Δ₂.ncard = 27 ∧
        (∀ x ∈ Δ₁, ∀ y ∈ Δ₁, ∃ n ∈ Nor (Op 2 (Nor U)), n * x * n⁻¹ = y) ∧
        (∀ x ∈ Δ₂, ∀ y ∈ Δ₂, ∃ n ∈ Nor (Op 2 (Nor U)), n * x * n⁻¹ = y) ∧
        (∀ x ∈ Δ₁, ∀ n ∈ Nor (Op 2 (Nor U)), n * x * n⁻¹ ∈ Δ₁) ∧
        (∀ x ∈ Δ₁, Op 2 (Cen x) = Op 2 (Nor U)) ∧ (∀ x ∈ Δ₂, Op 2 (Cen x) ≠ Op 2 (Nor U)) ∧
        (∀ x ∈ Op 2 (Nor U), x ≠ 1 →
          (x ∈ Δ₁ ↔ ncomp (Op 2 (Nor U)) b b₁ b₂ x % 2 = 1))

@[expose] def HypS49S6 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (b : G) (L B K : Subgroup G) (b₁ b₂ : G),
    FF84Post b L B K b₁ b₂ → ∀ U ∈ PiStar (Cen b) B 2, ∀ s₀ : G,
      s₀ ∈ ⁅Op 2 (Nor U), Subgroup.zpowers b⁆ → s₀ ≠ 1 →
        ∃ H : Subgroup G, H ≤ Cen s₀ ∧ Nonempty (↥H ≃* Equiv.Perm (Fin 6)) ∧
          H ⊓ Op 2 (Nor U) = ⊥

@[expose] def HypOmNormalizerE27 : Prop :=
  ∀ E : Subgroup (F6 ≃ₗ[ZMod 2] F6), E ≤ TauCeti.QuadraticMap.orthogonalGroup qMinusForm →
    IsElemAb 3 3 E →
      Nat.card ↥(Subgroup.normalizer (E : Set (F6 ≃ₗ[ZMod 2] F6)) ⊓
        TauCeti.QuadraticMap.orthogonalGroup qMinusForm) = 1296

@[expose] def HypOmPair : Prop :=
  ∀ {s t : F6}, qMinus s = 1 → qMinus t = 0 → qMinus (s + t) = 0 → t ≠ 0 →
    Nonempty ((MulAction.stabilizer OmG s ⊓ MulAction.stabilizer OmG t : Subgroup OmG) ≃*
      alternatingGroup (Fin 5))

@[expose] def HypOmParabolic : Prop :=
  ∀ {t : F6}, qMinus t = 0 → t ≠ 0 →
    IsElemAb 2 4 (Op 2 (MulAction.stabilizer OmG t)) ∧
      (∀ W : Subgroup OmG, W ≤ Op 2 (MulAction.stabilizer OmG t) →
        MulAction.stabilizer OmG t ≤ Nor W → W = ⊥ ∨ W = Op 2 (MulAction.stabilizer OmG t)) ∧
      (∀ g : OmG, (∀ x : F6, polarMinus x t = 0 → (g : F6 ≃ₗ[ZMod 2] F6) x = x) → g = 1) ∧
      AddSubgroup.closure {y : F6 | ∃ g ∈ Op 2 (MulAction.stabilizer OmG t), ∃ x : F6,
        y = (g : F6 ≃ₗ[ZMod 2] F6) x - x} = AddSubgroup.closure {x : F6 | polarMinus x t = 0}

end CFSG.RankThree.PartTwo.Sec21.FF84.S4

end
