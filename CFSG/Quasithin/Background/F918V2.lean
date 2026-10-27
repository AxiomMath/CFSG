module

public import CFSG.Foundations.Basic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin

private theorem center_eq_bot_of_simple {Q : Type*} [Group Q] [IsSimpleGroup Q] {a b : Q}
    (hab : a * b ≠ b * a) : Subgroup.center Q = ⊥ := by
  refine (IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center Q)).resolve_right fun htop => hab ?_
  have ha : a ∈ Subgroup.center Q := by
    rw [htop]
    exact Subgroup.mem_top a
  exact (Subgroup.mem_center_iff.1 ha b).symm

theorem ker_quot_eq_center {Lb Γ : Type*} [Group Lb] [Group Γ] (hq : CFSG.IsQuasisimple Lb)
    (θ : Lb →* Γ) (hθ : Function.Surjective θ) (hker : ∀ l, θ l = 1 → l ∈ Subgroup.center Lb) :
    ((QuotientGroup.mk' (Subgroup.center Γ)).comp θ).ker = Subgroup.center Lb := by
  ext l
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  constructor
  · intro hl
    have hsimple : IsSimpleGroup (Lb ⧸ Subgroup.center Lb) := hq.2.1
    obtain ⟨a, b, hab⟩ := hq.2.2
    have hmem : (l : Lb ⧸ Subgroup.center Lb) ∈ Subgroup.center (Lb ⧸ Subgroup.center Lb) := by
      rw [Subgroup.mem_center_iff]
      intro y
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
      apply hker
      rw [map_mul, map_inv, map_mul, map_mul, Subgroup.mem_center_iff.1 hl (θ x), inv_mul_cancel]
    rw [center_eq_bot_of_simple hab, Subgroup.mem_bot, QuotientGroup.eq_one_iff] at hmem
    exact hmem
  · intro hl
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨x, rfl⟩ := hθ g
    rw [← map_mul θ, ← map_mul θ, Subgroup.mem_center_iff.1 hl x]

theorem exists_alpha {Lb Γ : Type*} [Group Lb] [Group Γ] (θ₁ θ₂ : Lb →* Γ)
    (h1 : Function.Surjective θ₁) (h2 : Function.Surjective θ₂)
    (hk : ((QuotientGroup.mk' (Subgroup.center Γ)).comp θ₁).ker =
      ((QuotientGroup.mk' (Subgroup.center Γ)).comp θ₂).ker) :
    ∃ α : (Γ ⧸ Subgroup.center Γ) ≃* (Γ ⧸ Subgroup.center Γ),
      ∀ l, α (QuotientGroup.mk' (Subgroup.center Γ) (θ₁ l)) =
        QuotientGroup.mk' (Subgroup.center Γ) (θ₂ l) := by
  have s1 : Function.Surjective ((QuotientGroup.mk' (Subgroup.center Γ)).comp θ₁) :=
    (QuotientGroup.mk'_surjective _).comp h1
  have s2 : Function.Surjective ((QuotientGroup.mk' (Subgroup.center Γ)).comp θ₂) :=
    (QuotientGroup.mk'_surjective _).comp h2
  let e₁ := QuotientGroup.quotientKerEquivOfSurjective _ s1
  let e₂ := QuotientGroup.quotientKerEquivOfSurjective _ s2
  refine ⟨e₁.symm.trans ((QuotientGroup.quotientMulEquivOfEq hk).trans e₂), fun l => ?_⟩
  have he : e₁.symm (QuotientGroup.mk' (Subgroup.center Γ) (θ₁ l)) =
      (l : Lb ⧸ ((QuotientGroup.mk' (Subgroup.center Γ)).comp θ₁).ker) := by
    rw [MulEquiv.symm_apply_eq]
    rfl
  rw [MulEquiv.trans_apply, he, MulEquiv.trans_apply, QuotientGroup.quotientMulEquivOfEq_mk]
  rfl

theorem eq_of_central_ratio {Lb Γ : Type*} [Group Lb] [Group Γ]
    (hperf : Group.IsPerfect Lb) (θ θ' : Lb →* Γ)
    (h : ∀ l, θ l * (θ' l)⁻¹ ∈ Subgroup.center Γ) : θ = θ' := by
  let f : Lb →* Subgroup.center Γ := MonoidHom.mk' (fun l => ⟨θ l * (θ' l)⁻¹, h l⟩) fun a b => by
    apply Subtype.ext
    have hc := Subgroup.mem_center_iff.1 (h b) (θ' a)⁻¹
    simp only [map_mul, mul_inv_rev, Subgroup.coe_mul]
    rw [mul_assoc (θ a) (θ' a)⁻¹, hc]
    simp only [mul_assoc]
  ext l
  have hl : l ∈ f.ker :=
    Abelianization.commutator_subset_ker f (hperf.commutator_eq_top ▸ Subgroup.mem_top l)
  have h1 : θ l * (θ' l)⁻¹ = 1 := congrArg Subtype.val (MonoidHom.mem_ker.1 hl)
  exact mul_inv_eq_one.1 h1

end CFSG.Quasithin
