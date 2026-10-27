module

public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import Mathlib.FieldTheory.Finite.GaloisField

public section

namespace CFSG.StandardType.N2Chart

open Matrix

abbrev F4 : Type := GaloisField 2 2

abbrev V6 : Type := Fin 6 → F4

abbrev SL6 : Type := Matrix.SpecialLinearGroup (Fin 6) F4

@[expose] noncomputable def fixSp (g : SL6) : Submodule F4 V6 :=
  LinearMap.ker (Matrix.toLin' (g : Matrix (Fin 6) (Fin 6) F4) - LinearMap.id)

@[expose] noncomputable def suppSp (g : SL6) : Submodule F4 V6 :=
  LinearMap.range (Matrix.toLin' (g : Matrix (Fin 6) (Fin 6) F4) - LinearMap.id)

theorem mulVec_inv_mulVec (g : SL6) (v : V6) :
    ((g⁻¹ : SL6) : Matrix (Fin 6) (Fin 6) F4) *ᵥ ((g : Matrix (Fin 6) (Fin 6) F4) *ᵥ v) = v := by
  rw [Matrix.mulVec_mulVec, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
    Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec]

theorem mulVec_mulVec_inv (g : SL6) (v : V6) :
    (g : Matrix (Fin 6) (Fin 6) F4) *ᵥ (((g⁻¹ : SL6) : Matrix (Fin 6) (Fin 6) F4) *ᵥ v) = v := by
  rw [Matrix.mulVec_mulVec, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
    Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec]

@[expose] def stabSub (P E : Submodule F4 V6) : Subgroup SL6 where
  carrier := {g | (∀ v ∈ P, (g : Matrix (Fin 6) (Fin 6) F4) *ᵥ v = v) ∧
    (∀ v ∈ E, (g : Matrix (Fin 6) (Fin 6) F4) *ᵥ v ∈ E) ∧
    (∀ v ∈ E, ((g⁻¹ : SL6) : Matrix (Fin 6) (Fin 6) F4) *ᵥ v ∈ E)}
  mul_mem' := by
    rintro g h ⟨hgP, hgE, hgE'⟩ ⟨hhP, hhE, hhE'⟩
    refine ⟨fun v hv => ?_, fun v hv => ?_, fun v hv => ?_⟩
    · rw [Matrix.SpecialLinearGroup.coe_mul, ← Matrix.mulVec_mulVec, hhP v hv, hgP v hv]
    · rw [Matrix.SpecialLinearGroup.coe_mul, ← Matrix.mulVec_mulVec]
      exact hgE _ (hhE v hv)
    · rw [_root_.mul_inv_rev, Matrix.SpecialLinearGroup.coe_mul, ← Matrix.mulVec_mulVec]
      exact hhE' _ (hgE' v hv)
  one_mem' := by
    refine ⟨fun v _ => ?_, fun v hv => ?_, fun v hv => ?_⟩
    · rw [Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec]
    · rwa [Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec]
    · rwa [inv_one, Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec]
  inv_mem' := by
    rintro g ⟨hgP, hgE, hgE'⟩
    refine ⟨fun v hv => ?_, hgE', fun v hv => ?_⟩
    · conv_lhs => rw [← hgP v hv]
      exact mulVec_inv_mulVec g v
    · rw [inv_inv]
      exact hgE v hv

@[expose] def GGN2SliceLinesInput : Prop :=
  ∀ (u₁ u₂ : SL6) (T : Subgroup SL6), u₁ ^ 5 = 1 → u₂ ^ 5 = 1 →
    Module.finrank F4 (suppSp u₁) = 2 → Module.finrank F4 (suppSp u₂) = 2 →
    IsCompl (suppSp u₁) (fixSp u₁) → IsCompl (suppSp u₂) (fixSp u₂) →
    suppSp u₁ ≤ fixSp u₂ → suppSp u₂ ≤ fixSp u₁ →
    Nonempty (T ≃* Matrix.SpecialLinearGroup (Fin 3) F4) →
    T ≤ Subgroup.centralizer ({u₁} : Set SL6) →
    (∀ g ∈ T, ∀ v ∈ suppSp u₁, (g : Matrix (Fin 6) (Fin 6) F4) *ᵥ v = v) → u₂ ∈ T →
    ∃ b b' : Submodule F4 V6, b ≤ fixSp u₁ ⊓ fixSp u₂ ∧ b' ≤ fixSp u₁ ⊓ fixSp u₂ ∧
      Disjoint b b' ∧ Module.finrank F4 b = 1 ∧ Module.finrank F4 b' = 1 ∧
      T = stabSub (suppSp u₁ ⊔ b') (suppSp u₂ ⊔ b)

@[expose] def GGN2LineAlignmentInput : Prop :=
  ∀ A B a a' b b' : Submodule F4 V6,
    Module.finrank F4 A = 2 → Module.finrank F4 B = 2 → Module.finrank F4 a = 1 →
    Module.finrank F4 a' = 1 → Module.finrank F4 b = 1 → Module.finrank F4 b' = 1 →
    A ⊔ B ⊔ a ⊔ a' = ⊤ → b ≤ a ⊔ a' → b' ≤ a ⊔ a' → Disjoint b b' →
    (∀ z ∈ stabSub (B ⊔ a') (A ⊔ a), (∀ h ∈ stabSub (B ⊔ a') (A ⊔ a), Commute z h) →
      ∀ g ∈ stabSub (A ⊔ b') (B ⊔ b), z * g * z⁻¹ ∈ stabSub (A ⊔ b') (B ⊔ b)) →
    (∀ g ∈ stabSub (A ⊔ b') (B ⊔ b), ∀ h ∈ stabSub (B ⊔ a') (A ⊔ a), Commute g h) ∨
      (b = a ∧ b' = a' ∧
        stabSub a' (A ⊔ B ⊔ a) ≤ stabSub (A ⊔ b') (B ⊔ b) ⊔ stabSub (B ⊔ a') (A ⊔ a))

end CFSG.StandardType.N2Chart

end
