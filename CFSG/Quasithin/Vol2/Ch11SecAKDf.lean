module

public import CFSG.Quasithin.Vol2.Ch11SecAFacts03

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecA.C10KH

section Bar

variable {X W : Type} [Group X] [Group W] (ρ : X →* MulAut W)

theorem map_ker_of_iff {α : X ≃* X} (hα : ∀ x, x ∈ ρ.ker ↔ α x ∈ ρ.ker) :
    ρ.ker.map (α : X →* X) = ρ.ker := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (hα x).1 hx
  · intro hy
    refine ⟨α.symm y, (hα _).2 ?_, by simp⟩
    simpa using hy

@[expose] noncomputable def barAut (α : X ≃* X) (hα : ∀ x, x ∈ ρ.ker ↔ α x ∈ ρ.ker) :
    MulAut ↥ρ.range :=
  (QuotientGroup.quotientKerEquivRange ρ).symm.trans
    ((QuotientGroup.congr ρ.ker ρ.ker α (map_ker_of_iff ρ hα)).trans
      (QuotientGroup.quotientKerEquivRange ρ))

theorem barAut_apply (α : X ≃* X) (hα : ∀ x, x ∈ ρ.ker ↔ α x ∈ ρ.ker) (x : X) :
    barAut ρ α hα (ρ.rangeRestrict x) = ρ.rangeRestrict (α x) := by
  have h1 : (QuotientGroup.quotientKerEquivRange ρ).symm (ρ.rangeRestrict x) =
      (x : X ⧸ ρ.ker) := by
    rw [MulEquiv.symm_apply_eq]
    rfl
  rw [barAut, MulEquiv.trans_apply, MulEquiv.trans_apply, h1, QuotientGroup.congr_mk]
  rfl

theorem coe_barAut_apply (α : X ≃* X) (hα : ∀ x, x ∈ ρ.ker ↔ α x ∈ ρ.ker) (x : X) :
    ((barAut ρ α hα (ρ.rangeRestrict x) : ↥ρ.range) : MulAut W) = ρ (α x) := by
  rw [barAut_apply]
  rfl

@[expose] def indH (H : Subgroup (MulAut W)) : Subgroup (MulAut ↥H) where
  carrier := {β | ∃ φ : MulAut W, ∀ h : ↥H, ((β h : ↥H) : MulAut W) = φ * h * φ⁻¹}
  one_mem' := ⟨1, fun h => by simp⟩
  mul_mem' := by
    rintro a b ⟨φ, hφ⟩ ⟨ψ, hψ⟩
    refine ⟨φ * ψ, fun h => ?_⟩
    rw [MulAut.mul_apply, hφ (b h), hψ h]
    group
  inv_mem' := by
    rintro a ⟨φ, hφ⟩
    refine ⟨φ⁻¹, fun h => ?_⟩
    have := hφ (a⁻¹ h)
    rw [MulAut.apply_inv_self] at this
    rw [this]
    group

theorem isInducedOn_iff (α : X ≃* X) (hα : ∀ x, x ∈ ρ.ker ↔ α x ∈ ρ.ker) :
    IsInducedOn ρ α ↔ barAut ρ α hα ∈ indH ρ.range := by
  constructor
  · rintro ⟨φ, hφ⟩
    refine ⟨φ, fun h => ?_⟩
    obtain ⟨x, rfl⟩ := ρ.rangeRestrict_surjective h
    rw [coe_barAut_apply, hφ]
    rfl
  · rintro ⟨φ, hφ⟩
    refine ⟨φ, fun x => ?_⟩
    have := hφ (ρ.rangeRestrict x)
    rw [coe_barAut_apply] at this
    exact this

theorem barAut_trans (α₁ α₂ : X ≃* X) (h₁ : ∀ x, x ∈ ρ.ker ↔ α₁ x ∈ ρ.ker)
    (h₂ : ∀ x, x ∈ ρ.ker ↔ α₂ x ∈ ρ.ker) (h₁₂ : ∀ x, x ∈ ρ.ker ↔ (α₂.trans α₁) x ∈ ρ.ker) :
    barAut ρ (α₂.trans α₁) h₁₂ = barAut ρ α₁ h₁ * barAut ρ α₂ h₂ := by
  refine MulEquiv.ext fun h => ?_
  obtain ⟨x, rfl⟩ := ρ.rangeRestrict_surjective h
  rw [MulAut.mul_apply, barAut_apply, barAut_apply, barAut_apply]
  rfl

end Bar

theorem mul_mem_of_cover {G : Type*} [Group G] {S : Subgroup G} {τ : G}
    (hcov : ∀ θ : G, θ ∈ S ∨ θ * τ⁻¹ ∈ S) {a b : G} (ha : a ∉ S) (hb : b ∉ S) : a * b ∈ S := by
  have hτ : τ ∉ S := fun hτ => ha ((hcov a).elim id fun h => by
    have := S.mul_mem h hτ
    rwa [inv_mul_cancel_right] at this)
  have hx : a⁻¹ * τ⁻¹ ∈ S := (hcov a⁻¹).resolve_left fun h => ha (by simpa using S.inv_mem h)
  have hy : b * τ⁻¹ ∈ S := (hcov b).resolve_left hb
  rcases hcov (a * b) with h | h
  · exact h
  · exfalso
    apply hτ
    have he : τ⁻¹ = (a * b * τ⁻¹) * (b * τ⁻¹)⁻¹ * (a⁻¹ * τ⁻¹) := by group
    have h' : τ⁻¹ ∈ S := he ▸ S.mul_mem (S.mul_mem h (S.inv_mem hy)) hx
    simpa using S.inv_mem h'

theorem twist_of_cover {X W : Type} [Group X] [Group W] (ρ : X →* MulAut W)
    (hcov : ∃ τ : MulAut ↥ρ.range, ∀ θ, θ ∈ indH ρ.range ∨ θ * τ⁻¹ ∈ indH ρ.range)
    (α₁ α₂ : X ≃* X) (h₁ : ∀ x, x ∈ ρ.ker ↔ α₁ x ∈ ρ.ker)
    (h₂ : ∀ x, x ∈ ρ.ker ↔ α₂ x ∈ ρ.ker) (hn₁ : ¬ IsInducedOn ρ α₁)
    (hn₂ : ¬ IsInducedOn ρ α₂) : IsInducedOn ρ (α₂.trans α₁) := by
  obtain ⟨τ, hτ⟩ := hcov
  have h₁₂ : ∀ x, x ∈ ρ.ker ↔ (α₂.trans α₁) x ∈ ρ.ker := fun x => (h₂ x).trans (h₁ (α₂ x))
  rw [isInducedOn_iff ρ _ h₁₂, barAut_trans ρ α₁ α₂ h₁ h₂ h₁₂]
  exact mul_mem_of_cover hτ (fun h => hn₁ ((isInducedOn_iff ρ α₁ h₁).2 h))
    (fun h => hn₂ ((isInducedOn_iff ρ α₂ h₂).2 h))

section Model

variable {Γ M W : Type} [Group Γ] [Group M] [Group W]

@[expose] def indM (act : Γ →* MulAut M) : Subgroup (MulAut Γ) where
  carrier := {β | ∃ ψ : MulAut M, ∀ γ, act (β γ) = ψ * act γ * ψ⁻¹}
  one_mem' := ⟨1, fun γ => by simp⟩
  mul_mem' := by
    rintro a b ⟨φ, hφ⟩ ⟨ψ, hψ⟩
    refine ⟨φ * ψ, fun γ => ?_⟩
    rw [MulAut.mul_apply, hφ, hψ]
    group
  inv_mem' := by
    rintro a ⟨φ, hφ⟩
    refine ⟨φ⁻¹, fun γ => ?_⟩
    have := hφ (a⁻¹ γ)
    rw [MulAut.apply_inv_self] at this
    rw [this]
    group

theorem conj_mem_indM (act : Γ →* MulAut M) (c : Γ) : MulAut.conj c ∈ indM act :=
  ⟨act c, fun γ => by rw [MulAut.conj_apply, map_mul, map_mul, map_inv]⟩

theorem act_eq_congr {H : Subgroup (MulAut W)} (act : Γ →* MulAut M) (π : Γ ≃* ↥H)
    (e : W ≃* M) (he : ∀ γ w, e (((π γ : ↥H) : MulAut W) w) = act γ (e w)) (γ : Γ) :
    act γ = MulAut.congr e ((π γ : ↥H) : MulAut W) := by
  refine MulEquiv.ext fun m => ?_
  rw [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply, he,
    MulEquiv.apply_symm_apply]

theorem mem_indH_iff {H : Subgroup (MulAut W)} (act : Γ →* MulAut M) (π : Γ ≃* ↥H)
    (e : W ≃* M) (he : ∀ γ w, e (((π γ : ↥H) : MulAut W) w) = act γ (e w)) (θ : MulAut ↥H) :
    θ ∈ indH H ↔ MulAut.congr π.symm θ ∈ indM act := by
  have hc : ∀ γ, MulAut.congr π.symm θ γ = π.symm (θ (π γ)) := fun γ => rfl
  constructor
  · rintro ⟨φ, hφ⟩
    refine ⟨MulAut.congr e φ, fun γ => ?_⟩
    rw [hc, act_eq_congr act π e he, act_eq_congr act π e he, MulEquiv.apply_symm_apply, hφ,
      map_mul, map_mul, map_inv]
  · rintro ⟨ψ, hψ⟩
    refine ⟨(MulAut.congr e).symm ψ, fun h => ?_⟩
    apply (MulAut.congr e).injective
    have := hψ (π.symm h)
    rw [hc, act_eq_congr act π e he, act_eq_congr act π e he] at this
    simp only [MulEquiv.apply_symm_apply] at this
    rw [this, map_mul, map_mul, map_inv]
    simp only [MulEquiv.apply_symm_apply]

theorem cover_of_model {H : Subgroup (MulAut W)} (act : Γ →* MulAut M) (π : Γ ≃* ↥H)
    (e : W ≃* M) (he : ∀ γ w, e (((π γ : ↥H) : MulAut W) w) = act γ (e w))
    (hcov : ∃ τ : MulAut Γ, ∀ θ, θ ∈ indM act ∨ θ * τ⁻¹ ∈ indM act) :
    ∃ τ : MulAut ↥H, ∀ θ, θ ∈ indH H ∨ θ * τ⁻¹ ∈ indH H := by
  obtain ⟨τ, hτ⟩ := hcov
  refine ⟨(MulAut.congr π.symm).symm τ, fun θ => ?_⟩
  rw [mem_indH_iff act π e he, mem_indH_iff act π e he, map_mul, map_inv,
    MulEquiv.apply_symm_apply]
  exact hτ _

end Model

end CFSG.Quasithin.Vol2.Ch11.SecA.C10KH
