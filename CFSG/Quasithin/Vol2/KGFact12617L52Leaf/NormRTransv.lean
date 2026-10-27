module

public import CFSG.LieType.BorelTits.Basic

public section

namespace CFSG.Quasithin.H13.KG12617L52.NormR

open CFSG.LieType.BorelTits Module

section Transvection

variable {F V H : Type*} [Field F] [AddCommGroup V] [Module F V] [Group H]

theorem eq_zero_or_eq_one_of_card_eq_two (hF : Nat.card F = 2) (c : F) : c = 0 ∨ c = 1 := by
  obtain ⟨y, -, hy'⟩ := (Nat.card_eq_two_iff' (0 : F)).1 hF
  by_cases hc : c = 0
  · exact Or.inl hc
  · exact Or.inr ((hy' c hc).trans (hy' 1 one_ne_zero).symm)

theorem one_add_one_of_card_eq_two (hF : Nat.card F = 2) : (1 : F) + 1 = 0 := by
  rcases eq_zero_or_eq_one_of_card_eq_two hF (1 + 1) with h | h
  · exact h
  · exact absurd (by simpa using h : (1 : F) = 0) one_ne_zero

theorem rep_eq_zero {ρ : H →* Module.End F V} {r : H} {v : V} (h : ρ r v = 0) : v = 0 := by
  have := congrArg (ρ r⁻¹) h
  rwa [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply,
    map_zero] at this

@[expose] def tvForms (ρ : H →* Module.End F V) (R : Subgroup H) (v₁ : V) :
    Set (Module.Dual F V) :=
  {φ | ∃ r ∈ R, ∀ v, ρ r v = v + φ v • v₁}

@[expose] def tvFix (ρ : H →* Module.End F V) (R : Subgroup H) (v₁ : V) : Submodule F V where
  carrier := {w | ∀ φ ∈ tvForms ρ R v₁, φ w = 0}
  zero_mem' := fun φ _ => map_zero φ
  add_mem' := fun ha hb φ hφ => by rw [map_add, ha φ hφ, hb φ hφ, add_zero]
  smul_mem' := fun c w hw φ hφ => by rw [map_smul, hw φ hφ, smul_zero]

variable {ρ : H →* Module.End F V} {R : Subgroup H} {v₁ : V}

theorem apply_center_of_mem_tvForms (hF : Nat.card F = 2) (hv₁ : v₁ ≠ 0) {φ : Module.Dual F V}
    (hφ : φ ∈ tvForms ρ R v₁) : φ v₁ = 0 := by
  obtain ⟨r, -, h⟩ := hφ
  rcases eq_zero_or_eq_one_of_card_eq_two hF (φ v₁) with h0 | h0
  · exact h0
  · exfalso
    have h1 := h v₁
    rw [h0, one_smul] at h1
    have h2 : v₁ + v₁ = 0 := by
      calc v₁ + v₁ = (1 + 1 : F) • v₁ := by rw [add_smul, one_smul]
        _ = 0 := by rw [one_add_one_of_card_eq_two hF, zero_smul]
    rw [h2] at h1
    exact hv₁ (rep_eq_zero h1)

theorem center_mem_tvFix (hF : Nat.card F = 2) (hv₁ : v₁ ≠ 0) : v₁ ∈ tvFix ρ R v₁ :=
  fun _ hφ => apply_center_of_mem_tvForms hF hv₁ hφ

theorem zero_mem_tvForms : (0 : Module.Dual F V) ∈ tvForms ρ R v₁ :=
  ⟨1, R.one_mem, fun v => by simp⟩

theorem add_mem_tvForms (hF : Nat.card F = 2) (hv₁ : v₁ ≠ 0) {φ ψ : Module.Dual F V}
    (hφ : φ ∈ tvForms ρ R v₁) (hψ : ψ ∈ tvForms ρ R v₁) : φ + ψ ∈ tvForms ρ R v₁ := by
  have hφ' := hφ
  obtain ⟨r, hr, h⟩ := hφ
  obtain ⟨s, hs, h'⟩ := hψ
  have hr1 : ρ r v₁ = v₁ := by
    have := h v₁
    rwa [apply_center_of_mem_tvForms hF hv₁ hφ', zero_smul, add_zero] at this
  refine ⟨r * s, R.mul_mem hr hs, fun v => ?_⟩
  calc ρ (r * s) v = ρ r (ρ s v) := by rw [map_mul, Module.End.mul_apply]
    _ = ρ r (v + ψ v • v₁) := by rw [h' v]
    _ = ρ r v + ψ v • ρ r v₁ := by rw [map_add, map_smul]
    _ = (v + φ v • v₁) + ψ v • v₁ := by rw [h v, hr1]
    _ = v + (φ + ψ) v • v₁ := by rw [LinearMap.add_apply, add_smul, add_assoc]

theorem mem_tvForms_of_forall_tvFix [FiniteDimensional F V] (hF : Nat.card F = 2) (hv₁ : v₁ ≠ 0)
    {ψ : Module.Dual F V} (hψ : ∀ w ∈ tvFix ρ R v₁, ψ w = 0) : ψ ∈ tvForms ρ R v₁ := by
  let Ψ : Submodule F (Module.Dual F V) :=
    { carrier := tvForms ρ R v₁
      zero_mem' := zero_mem_tvForms
      add_mem' := fun ha hb => add_mem_tvForms hF hv₁ ha hb
      smul_mem' := fun c φ hφ => by
        rcases eq_zero_or_eq_one_of_card_eq_two hF c with rfl | rfl
        · rw [zero_smul]; exact zero_mem_tvForms
        · rw [one_smul]; exact hφ }
  have hΨ : Ψ.dualCoannihilator = tvFix ρ R v₁ := by
    ext w
    rw [Submodule.mem_dualCoannihilator]
    exact Iff.rfl
  have h : ψ ∈ Ψ.dualCoannihilator.dualAnnihilator := by
    rw [Submodule.mem_dualAnnihilator]
    intro w hw
    rw [hΨ] at hw
    exact hψ w hw
  rw [Subspace.dualCoannihilator_dualAnnihilator_eq] at h
  exact h

theorem conj_mem_of_stab [FiniteDimensional F V] (hF : Nat.card F = 2)
    (hρ : Function.Injective ρ) (hv₁ : v₁ ≠ 0)
    (hR : ∀ r ∈ R, ∃ φ : Module.Dual F V, ∀ v, ρ r v = v + φ v • v₁) {g : H}
    (hg₁ : ρ g v₁ = v₁) (hgW : ∀ w ∈ tvFix ρ R v₁, ρ g⁻¹ w ∈ tvFix ρ R v₁) {r : H}
    (hr : r ∈ R) : g * r * g⁻¹ ∈ R := by
  obtain ⟨φ, hφ⟩ := hR r hr
  have hφT : φ ∈ tvForms ρ R v₁ := ⟨r, hr, hφ⟩
  have hψ : φ.comp (ρ g⁻¹) ∈ tvForms ρ R v₁ :=
    mem_tvForms_of_forall_tvFix hF hv₁ fun w hw => hgW w hw φ hφT
  obtain ⟨r', hr', hr'ψ⟩ := hψ
  have hgg : ∀ y, ρ g (ρ g⁻¹ y) = y := fun y => by
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  have : g * r * g⁻¹ = r' := by
    apply hρ
    refine LinearMap.ext fun v => ?_
    calc ρ (g * r * g⁻¹) v = ρ g (ρ r (ρ g⁻¹ v)) := by
          rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply]
      _ = ρ g (ρ g⁻¹ v + φ (ρ g⁻¹ v) • v₁) := by rw [hφ]
      _ = v + φ (ρ g⁻¹ v) • v₁ := by rw [map_add, map_smul, hgg, hg₁]
      _ = ρ r' v := (hr'ψ v).symm
  rw [this]
  exact hr'

theorem mem_normalizer_of_stab [FiniteDimensional F V] (hF : Nat.card F = 2)
    (hρ : Function.Injective ρ) (hv₁ : v₁ ≠ 0)
    (hR : ∀ r ∈ R, ∃ φ : Module.Dual F V, ∀ v, ρ r v = v + φ v • v₁) {g : H}
    (hg₁ : ρ g v₁ = v₁)
    (hgW : ∀ w ∈ tvFix ρ R v₁, ρ g w ∈ tvFix ρ R v₁ ∧ ρ g⁻¹ w ∈ tvFix ρ R v₁) :
    g ∈ Subgroup.normalizer (R : Set H) := by
  have hg₁' : ρ g⁻¹ v₁ = v₁ := by
    conv_lhs => rw [← hg₁]
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · exact fun hh => conj_mem_of_stab hF hρ hv₁ hR hg₁ (fun w hw => (hgW w hw).2) hh
  · intro hconj
    have := conj_mem_of_stab hF hρ hv₁ hR hg₁' (g := g⁻¹)
      (fun w hw => by simpa using (hgW w hw).1) hconj
    simpa [mul_assoc] using this

end Transvection

end CFSG.Quasithin.H13.KG12617L52.NormR
