module

public import CFSG.LocalAnalysis.WeakClosure81.Thirteen
public import CFSG.LocalAnalysis.WeakClosure81.EightEightDefs

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.SignalizerFunctorTheorem.Quadratic CFSG.Quasithin.G11 CFSG.Quasithin CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22 (Bar2)

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

@[expose] noncomputable def mOfG {G : Type*} [Group G] (A B : Subgroup G) : ℕ :=
  Nat.log 2 ((B.subgroupOf A).index)

theorem mOf_eq_mOfG (A B : Subgroup (LGL 2 V)) : mOf A B = mOfG A B := rfl

@[expose] def PairQuotOK {G : Type} [Group G] (k₁ k₂ : ℕ) (X : Subgroup G) : Prop :=
  (k₁ = 1 ∧ k₂ = 1 ∧
    (IsPGroup 2 X ∨ ∃ r : ℕ, Odd r ∧ 1 < r ∧ Nonempty (Bar2 X ≃* DihedralGroup r))) ∨
    (k₁ + k₂ = 3 ∧ Nat.card (Bar2 X) = 60) ∨
    (k₁ = 2 ∧ k₂ = 2 ∧ (Nat.card (Bar2 X) = 60 ∨ Nat.card (Bar2 X) = 504))

@[expose] def PairViolation {G : Type} [Group G] (A : Subgroup G) (y : G) : Prop :=
  ¬ A.map (MulAut.conj y).toMonoidHom ≤ Subgroup.normalizer (A : Set G) ∧
  ¬ A ≤ Subgroup.normalizer (A.map (MulAut.conj y).toMonoidHom : Set G) ∧
  mOfG A (A ⊓ Subgroup.normalizer (A.map (MulAut.conj y).toMonoidHom : Set G)) ≤ 2 ∧
  mOfG (A.map (MulAut.conj y).toMonoidHom)
    (A.map (MulAut.conj y).toMonoidHom ⊓ Subgroup.normalizer (A : Set G)) ≤ 2 ∧
  ¬ PairQuotOK
    (mOfG A (A ⊓ Subgroup.normalizer (A.map (MulAut.conj y).toMonoidHom : Set G)))
    (mOfG (A.map (MulAut.conj y).toMonoidHom)
      (A.map (MulAut.conj y).toMonoidHom ⊓ Subgroup.normalizer (A : Set G)))
    (A ⊔ A.map (MulAut.conj y).toMonoidHom)

@[expose] def PairTest (Y : Subgroup (LGL 2 V)) (Γ : Set (Subgroup (LGL 2 V))) : Prop :=
  ∀ A ∈ Γ, ∀ y ∈ Y, ¬ PairViolation A y

structure Br1Base (Y : Subgroup (LGL 2 V)) (Γ : Set (Subgroup (LGL 2 V)))
    (VA : Subgroup (LGL 2 V) → Submodule (ZMod 2) V) (T : Subgroup (LGL 2 V))
    (𝒢 : Set (Subgroup (LGL 2 V))) (Zs : Submodule (ZMod 2) V) (m i₀ : ℕ)
    (δ : Subgroup (LGL 2 V) → ℕ) : Prop where
  hmi : i₀ + 3 ≤ m
  h131 : Assumption131 Y Γ VA (m - i₀ - 1)
  vfix : ∀ A ∈ Γ, VA A ≤ fixSub A
  delta_le : ∀ D ∈ Γ, δ D ≤ i₀
  comm_le : ∀ D ∈ Γ, ∀ B : Subgroup (LGL 2 V), B ≤ D → mOf D B + δ D < m →
    commSpace D (fixSub B) ≤ VA D
  sylow : IsSylowIn 2 T Y
  gens : ∀ B ∈ 𝒢, B ≤ T ∧ ∃ D ∈ Γ, B ≤ D ∧ mOf D B + δ D ≤ i₀
  weakClosure : ∀ A ∈ Γ, A ≤ T →
    (∀ B ∈ 𝒢, B ≤ Subgroup.normalizer (A : Set (LGL 2 V))) →
    ∀ X : Subgroup (LGL 2 V), X ≤ Y → T ≤ X → X ≠ Y →
      X ≤ Subgroup.normalizer (A : Set (LGL 2 V))
  zs_eq : Zs = fixSub T
  zs_gen : (⨆ y ∈ Y, conjSub y Zs) = ⊤
  zs_nofix : ∀ w ∈ Zs, w ≠ 0 → ∃ y ∈ Y, y w ≠ w

structure Br2Common (Y : Subgroup (LGL 2 V)) (Γ : Set (Subgroup (LGL 2 V)))
    (VA : Subgroup (LGL 2 V) → Submodule (ZMod 2) V) (T : Subgroup (LGL 2 V))
    (𝒢 : Set (Subgroup (LGL 2 V))) (Zs : Submodule (ZMod 2) V) (m i₀ : ℕ)
    (δ : Subgroup (LGL 2 V) → ℕ) : Prop extends Br1Base Y Γ VA T 𝒢 Zs m i₀ δ where
  noOffender : ∀ D ∈ Γ, ∃ B : Subgroup (LGL 2 V), B ≤ D ∧ mOf D B ≤ 2 ∧ fixSub D ≠ fixSub B

structure Br2OneComp (Y T L : Subgroup (LGL 2 V)) : Prop where
  le : L ≤ Y
  normal : ∀ y ∈ Y, ∀ l ∈ L, y * l * y⁻¹ ∈ L
  simple : IsSimpleGroup ↥L
  nonab : ∃ a ∈ L, ∃ b ∈ L, a * b ≠ b * a
  cent : ∀ y ∈ Y, (∀ l ∈ L, y * l = l * y) → y = 1
  dynkin : ∃ τ ∈ T, ActsOnDynkinMod ⊥ L τ

structure Br2TwoComp (Y T L₁ L₂ : Subgroup (LGL 2 V)) : Prop where
  le₁ : L₁ ≤ Y
  le₂ : L₂ ≤ Y
  simple₁ : IsSimpleGroup ↥L₁
  simple₂ : IsSimpleGroup ↥L₂
  nonab₁ : ∃ a ∈ L₁, ∃ b ∈ L₁, a * b ≠ b * a
  nonab₂ : ∃ a ∈ L₂, ∃ b ∈ L₂, a * b ≠ b * a
  comm : ∀ a ∈ L₁, ∀ b ∈ L₂, a * b = b * a
  ne : L₁ ≠ L₂
  perm : ∀ y ∈ Y, (cj y L₁ = L₁ ∧ cj y L₂ = L₂) ∨ (cj y L₁ = L₂ ∧ cj y L₂ = L₁)
  swap : ∃ x ∈ T, cj x L₁ = L₂
  cent : ∀ y ∈ Y, (∀ l ∈ L₁, y * l = l * y) → (∀ l ∈ L₂, y * l = l * y) → y = 1
  gen : ∀ y ∈ Y, ∃ l ∈ L₁ ⊔ L₂, ∃ t ∈ T, y = l * t

structure Br2ED (Γ : Set (Subgroup (LGL 2 V)))
    (VA : Subgroup (LGL 2 V) → Submodule (ZMod 2) V) (m : ℕ) (δ : Subgroup (LGL 2 V) → ℕ)
    (ED : Subgroup (LGL 2 V) → Submodule (ZMod 2) V) : Prop where
  comm_le : ∀ D ∈ Γ, commSpace D (ED D) ≤ VA D
  rank : ∀ D ∈ Γ, ∀ e : V, e ∉ ED D →
    m ≤ Module.finrank (ZMod 2)
      (Submodule.span (ZMod 2) {w : V | ∃ d ∈ D, w = d e - e}) + δ D

end CFSG.LocalAnalysis.WeakClosure81

end
