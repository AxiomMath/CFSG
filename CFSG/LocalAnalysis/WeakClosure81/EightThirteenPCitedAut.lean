module

public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.WeakClosure81.SevenDefs
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.WeakClosure81

@[expose] def OuterFixedNotElem (M : Type) [Group M] : Prop :=
  ∀ β : MulAut M, β * β = 1 → (¬ ∃ g : M, ∀ x : M, β x = g * x * g⁻¹) →
    ∃ x : M, β x = x ∧ x * x ≠ 1

@[expose] def OuterFixedNoNormalTwo (M : Type) [Group M] : Prop :=
  ∀ β : MulAut M, β * β = 1 → (¬ ∃ g : M, ∀ x : M, β x = g * x * g⁻¹) →
    ∀ E : Subgroup M, IsPGroup 2 E → (∀ x ∈ E, β x = x) →
      (∀ y : M, β y = y → ∀ x ∈ E, y * x * y⁻¹ ∈ E) → E = ⊥

@[expose] def OuterFixedRigid (M : Type) [Group M] : Prop :=
  ∀ β : MulAut M, β * β = 1 → (¬ ∃ g : M, ∀ x : M, β x = g * x * g⁻¹) →
    ∀ γ : MulAut M, γ * γ = 1 → γ * β = β * γ → (∀ x : M, β x = x → γ x = x) →
      γ = 1 ∨ γ = β

private lemma wcci_congr_apply {M M' : Type*} [Group M] [Group M'] (e : M ≃* M')
    (β : MulAut M) (y : M') :
    (MulAut.congr e) β y = e (β (e.symm y)) := by
  rw [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply]

private lemma wcci_congr_symm_apply {M M' : Type*} [Group M] [Group M'] (e : M ≃* M')
    (β' : MulAut M') (y : M) :
    (MulAut.congr e).symm β' y = e.symm (β' (e y)) := by
  rw [MulAut.congr_symm_apply, MulEquiv.trans_apply, MulEquiv.trans_apply]

private lemma wcci_congr_apply_mk {M M' : Type*} [Group M] [Group M'] (e : M ≃* M')
    (β : MulAut M) (x : M) :
    (MulAut.congr e) β (e x) = e (β x) := by
  rw [wcci_congr_apply, MulEquiv.symm_apply_apply]

private lemma wcci_congr_symm_mul_self {M M' : Type*} [Group M] [Group M'] (e : M ≃* M')
    (β' : MulAut M') (h : β' * β' = 1) :
    (MulAut.congr e).symm β' * (MulAut.congr e).symm β' = 1 := by
  apply (MulAut.congr e).injective
  rw [map_mul, MulEquiv.apply_symm_apply, h, map_one]

private lemma wcci_outer_iff {M M' : Type*} [Group M] [Group M'] (e : M ≃* M')
    (β : MulAut M) (β' : MulAut M') (hφ : (MulAut.congr e) β = β') :
    (∃ g : M, ∀ x : M, β x = g * x * g⁻¹) ↔
      (∃ g : M', ∀ x : M', β' x = g * x * g⁻¹) := by
  constructor
  · rintro ⟨g, hg⟩
    refine ⟨e g, fun y => ?_⟩
    rw [← hφ, wcci_congr_apply, hg (e.symm y)]
    simp
  · rintro ⟨g, hg⟩
    refine ⟨e.symm g, fun x => ?_⟩
    rw [← MulEquiv.symm_apply_apply (MulAut.congr e) β, hφ, wcci_congr_symm_apply,
      hg (e x)]
    simp

theorem outerFixedNotElem_of_mulEquiv {M M' : Type} [Group M] [Group M'] (e : M ≃* M')
    (h : OuterFixedNotElem M) : OuterFixedNotElem M' := by
  intro β' hβ'2 hβ'outer
  let β : MulAut M := (MulAut.congr e).symm β'
  have hφβ : (MulAut.congr e) β = β' := MulEquiv.apply_symm_apply (MulAut.congr e) β'
  have hβ2 : β * β = 1 := wcci_congr_symm_mul_self e β' hβ'2
  have hβouter : ¬ ∃ g : M, ∀ x : M, β x = g * x * g⁻¹ :=
    fun hh => hβ'outer ((wcci_outer_iff e β β' hφβ).1 hh)
  obtain ⟨x, hxβ, hx2⟩ := h β hβ2 hβouter
  refine ⟨e x, ?_, ?_⟩
  · rw [← hφβ, wcci_congr_apply_mk, hxβ]
  · intro hxx
    exact hx2 (e.injective (by rw [map_mul, map_one, hxx]))

theorem outerFixedNoNormalTwo_of_mulEquiv {M M' : Type} [Group M] [Group M'] (e : M ≃* M')
    (h : OuterFixedNoNormalTwo M) : OuterFixedNoNormalTwo M' := by
  intro β' hβ'2 hβ'outer E' hE'2 hE'fix hE'norm
  let β : MulAut M := (MulAut.congr e).symm β'
  have hφβ : (MulAut.congr e) β = β' := MulEquiv.apply_symm_apply (MulAut.congr e) β'
  have hβ2 : β * β = 1 := wcci_congr_symm_mul_self e β' hβ'2
  have hβouter : ¬ ∃ g : M, ∀ x : M, β x = g * x * g⁻¹ :=
    fun hh => hβ'outer ((wcci_outer_iff e β β' hφβ).1 hh)
  let E : Subgroup M := E'.map e.symm.toMonoidHom
  have hE2 : IsPGroup 2 E := IsPGroup.map hE'2 e.symm.toMonoidHom
  have hEfix : ∀ x ∈ E, β x = x := by
    intro x hx
    obtain ⟨x', hx', rfl⟩ := Subgroup.mem_map.1 hx
    change e.symm (β' (e (e.symm x'))) = e.symm x'
    rw [MulEquiv.apply_symm_apply, hE'fix x' hx']
  have hEnorm : ∀ y : M, β y = y → ∀ x ∈ E, y * x * y⁻¹ ∈ E := by
    intro y hy x hx
    obtain ⟨x', hx', rfl⟩ := Subgroup.mem_map.1 hx
    have hy' : β' (e y) = e y := by
      rw [← hφβ, wcci_congr_apply_mk, hy]
    refine Subgroup.mem_map.2 ⟨e y * x' * (e y)⁻¹, hE'norm (e y) hy' x' hx', ?_⟩
    simp
  have hEbot : E = ⊥ := h β hβ2 hβouter E hE2 hEfix hEnorm
  exact (Subgroup.map_eq_bot_iff_of_injective (H := E') e.symm.injective).1 hEbot

theorem outerFixedRigid_of_mulEquiv {M M' : Type} [Group M] [Group M'] (e : M ≃* M')
    (h : OuterFixedRigid M) : OuterFixedRigid M' := by
  intro β' hβ'2 hβ'outer γ' hγ'2 hγ'β' hγ'fix
  let β : MulAut M := (MulAut.congr e).symm β'
  let γ : MulAut M := (MulAut.congr e).symm γ'
  have hφβ : (MulAut.congr e) β = β' := MulEquiv.apply_symm_apply (MulAut.congr e) β'
  have hφγ : (MulAut.congr e) γ = γ' := MulEquiv.apply_symm_apply (MulAut.congr e) γ'
  have hβ2 : β * β = 1 := wcci_congr_symm_mul_self e β' hβ'2
  have hβouter : ¬ ∃ g : M, ∀ x : M, β x = g * x * g⁻¹ :=
    fun hh => hβ'outer ((wcci_outer_iff e β β' hφβ).1 hh)
  have hγ2 : γ * γ = 1 := by
    apply (MulAut.congr e).injective
    rw [map_mul, hφγ, hγ'2, map_one]
  have hγβ : γ * β = β * γ := by
    apply (MulAut.congr e).injective
    rw [map_mul, map_mul, hφγ, hφβ, hγ'β']
  have hγfix : ∀ x : M, β x = x → γ x = x := by
    intro x hx
    have hx' : β' (e x) = e x := by
      rw [← hφβ, wcci_congr_apply_mk, hx]
    have hγx : γ' (e x) = e x := hγ'fix (e x) hx'
    exact e.injective (by rw [← wcci_congr_apply_mk, hφγ, hγx])
  rcases h β hβ2 hβouter γ hγ2 hγβ hγfix with h1 | h1
  · left
    rw [← hφγ, h1, map_one]
  · right
    rw [← hφγ, ← hφβ, h1]

end CFSG.LocalAnalysis.WeakClosure81

end
