module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Quasithin.Vol2.Ch10SecEFix

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecE

open CFSG.Quasithin

section ProdEquiv

variable {X : Type*} [Group X] {P₁ P₂ : Subgroup X}

theorem prodSup_comm (hc : ∀ a ∈ P₁, ∀ b ∈ P₂, a * b = b * a) :
    ∀ (a : ↥P₁) (b : ↥P₂), Commute (P₁.subtype a) (P₂.subtype b) :=
  fun a b => hc a a.2 b b.2

theorem prodSup_injective (hc : ∀ a ∈ P₁, ∀ b ∈ P₂, a * b = b * a) (hi : P₁ ⊓ P₂ = ⊥) :
    Function.Injective (MonoidHom.noncommCoprod P₁.subtype P₂.subtype (prodSup_comm hc)) := by
  rw [MonoidHom.noncommCoprod_injective]
  refine ⟨P₁.subtype_injective, P₂.subtype_injective, ?_⟩
  rw [Subgroup.range_subtype, Subgroup.range_subtype, disjoint_iff]
  exact hi

theorem prodSup_range (hc : ∀ a ∈ P₁, ∀ b ∈ P₂, a * b = b * a) :
    (MonoidHom.noncommCoprod P₁.subtype P₂.subtype (prodSup_comm hc)).range = P₁ ⊔ P₂ := by
  rw [MonoidHom.noncommCoprod_range, Subgroup.range_subtype, Subgroup.range_subtype]

noncomputable def prodEquivSup (hc : ∀ a ∈ P₁, ∀ b ∈ P₂, a * b = b * a) (hi : P₁ ⊓ P₂ = ⊥) :
    ↥P₁ × ↥P₂ ≃* ↥(P₁ ⊔ P₂) :=
  (MonoidHom.ofInjective (prodSup_injective hc hi)).trans
    (MulEquiv.subgroupCongr (prodSup_range hc))

theorem coe_prodEquivSup (hc : ∀ a ∈ P₁, ∀ b ∈ P₂, a * b = b * a) (hi : P₁ ⊓ P₂ = ⊥)
    (p : ↥P₁ × ↥P₂) : (prodEquivSup hc hi p : X) = (p.1 : X) * p.2 := by
  show ((MonoidHom.ofInjective (prodSup_injective hc hi) p :
    ↥(MonoidHom.noncommCoprod P₁.subtype P₂.subtype (prodSup_comm hc)).range) : X) = _
  rw [MonoidHom.ofInjective_apply, MonoidHom.noncommCoprod_apply]
  rfl

end ProdEquiv

section Decomp

variable {X : Type*} [Group X] {P₁ P₂ : Subgroup X}

theorem eq_mul_prodEquivSup_symm (hc : ∀ a ∈ P₁, ∀ b ∈ P₂, a * b = b * a) (hi : P₁ ⊓ P₂ = ⊥)
    (x : ↥(P₁ ⊔ P₂)) :
    (x : X) = (((prodEquivSup hc hi).symm x).1 : X) * ((prodEquivSup hc hi).symm x).2 := by
  rw [← coe_prodEquivSup hc hi, MulEquiv.apply_symm_apply]

theorem eq_of_mul_eq_mul (hi : P₁ ⊓ P₂ = ⊥) {a a' b b' : X} (ha : a ∈ P₁) (ha' : a' ∈ P₁)
    (hb : b ∈ P₂) (hb' : b' ∈ P₂) (h : a * b = a' * b') : a = a' ∧ b = b' := by
  have h1 : a'⁻¹ * a = b' * b⁻¹ := by
    calc a'⁻¹ * a = a'⁻¹ * (a * b) * b⁻¹ := by group
      _ = a'⁻¹ * (a' * b') * b⁻¹ := by rw [h]
      _ = b' * b⁻¹ := by group
  have h2 : a'⁻¹ * a ∈ P₁ ⊓ P₂ :=
    ⟨P₁.mul_mem (P₁.inv_mem ha') ha, h1 ▸ P₂.mul_mem hb' (P₂.inv_mem hb)⟩
  rw [hi, Subgroup.mem_bot] at h2
  have e1 : a = a' := by
    calc a = a' * (a'⁻¹ * a) := by group
      _ = a' := by rw [h2, mul_one]
  subst e1
  exact ⟨rfl, mul_left_cancel h⟩

end Decomp

end CFSG.Quasithin.Vol2.Ch10.SecE
