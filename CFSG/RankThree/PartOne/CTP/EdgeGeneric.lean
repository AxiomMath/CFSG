module

public import Mathlib.GroupTheory.Subgroup.Center
public import Mathlib.Tactic.Group

public section

namespace CFSG.RankThree.PartOne.CTP

section Conj

variable {S G : Type*} [Group S] [Group G] {θ : S →* G}

theorem commute_of_conj (hθ : Function.Injective θ) {e : G} {g : S}
    (hg : ∀ s, θ (g * s * g⁻¹) = e * θ s * e⁻¹) {a : S} (hea : e * θ a = θ a * e) :
    a * g = g * a := by
  have h1 := hg a
  have h2 : e * θ a * e⁻¹ = θ a := by
    rw [mul_inv_eq_iff_eq_mul]
    exact hea
  rw [h2] at h1
  have h3 := hθ h1
  rw [mul_inv_eq_iff_eq_mul] at h3
  exact h3.symm

theorem not_commute_of_conj {e : G} {g : S}
    (hg : ∀ s, θ (g * s * g⁻¹) = e * θ s * e⁻¹) {b : S} (hb : e * θ b ≠ θ b * e) :
    g * b ≠ b * g := by
  intro h
  apply hb
  have h1 : g * b * g⁻¹ = b := by rw [mul_inv_eq_iff_eq_mul]; exact h
  have h2 := hg b
  rw [h1] at h2
  rw [eq_mul_inv_iff_mul_eq] at h2
  exact h2.symm

theorem commute_of_conj_of_center_bot (hθ : Function.Injective θ)
    (hS : Subgroup.center S = ⊥) {eA eB : G} {gA gB : S}
    (hgA : ∀ s, θ (gA * s * gA⁻¹) = eA * θ s * eA⁻¹)
    (hgB : ∀ s, θ (gB * s * gB⁻¹) = eB * θ s * eB⁻¹) (hee : eA * eB = eB * eA) :
    gA * gB = gB * gA := by
  have h1 : ∀ s, (gB * gA) * s * (gB * gA)⁻¹ = (gA * gB) * s * (gA * gB)⁻¹ := by
    intro s
    apply hθ
    have e1 : (gA * gB) * s * (gA * gB)⁻¹ = gA * (gB * s * gB⁻¹) * gA⁻¹ := by group
    have e2 : (gB * gA) * s * (gB * gA)⁻¹ = gB * (gA * s * gA⁻¹) * gB⁻¹ := by group
    rw [e1, e2, hgA, hgB, hgB, hgA]
    have e3 : eB * (eA * θ s * eA⁻¹) * eB⁻¹ = (eB * eA) * θ s * (eB * eA)⁻¹ := by group
    have e4 : eA * (eB * θ s * eB⁻¹) * eA⁻¹ = (eA * eB) * θ s * (eA * eB)⁻¹ := by group
    rw [e3, e4, hee]
  have hzc : (gB * gA)⁻¹ * (gA * gB) ∈ Subgroup.center S := by
    rw [Subgroup.mem_center_iff]
    intro s
    have h2 := h1 s
    have h3 : (gB * gA)⁻¹ * (gA * gB) * s * ((gB * gA)⁻¹ * (gA * gB))⁻¹ = s := by
      calc (gB * gA)⁻¹ * (gA * gB) * s * ((gB * gA)⁻¹ * (gA * gB))⁻¹
          = (gB * gA)⁻¹ * ((gA * gB) * s * (gA * gB)⁻¹) * (gB * gA) := by group
        _ = (gB * gA)⁻¹ * ((gB * gA) * s * (gB * gA)⁻¹) * (gB * gA) := by rw [← h2]
        _ = s := by group
    rw [mul_inv_eq_iff_eq_mul] at h3
    exact h3.symm
  rw [hS] at hzc
  exact (inv_mul_eq_one.mp (Subgroup.mem_bot.mp hzc)).symm

end Conj

section Lift

variable {S G : Type*} [Group S] [Group G]

theorem exists_lift_of_equiv (θ : S →* G) (hθ : Function.Injective θ) {A : Subgroup G}
    (hAle : A ≤ θ.range) {L : Type*} [Group L] (ρ : L ≃* ↥A) :
    ∃ φ : L →* S, Function.Injective φ ∧ (∀ a, θ (φ a) = (ρ a : G)) ∧
      A.comap θ = φ.range := by
  let φ : L →* S := (MonoidHom.ofInjective hθ).symm.toMonoidHom.comp
    ((Subgroup.inclusion hAle).comp ρ.toMonoidHom)
  have hθφ : ∀ a, θ (φ a) = (ρ a : G) := fun a => by
    change θ ((MonoidHom.ofInjective hθ).symm (Subgroup.inclusion hAle (ρ a))) = _
    rw [MonoidHom.apply_ofInjective_symm]
    rfl
  refine ⟨φ, fun a a' h => ρ.injective (Subtype.ext (by rw [← hθφ a, ← hθφ a', h])), hθφ, ?_⟩
  ext s
  constructor
  · intro hs
    refine ⟨ρ.symm ⟨θ s, hs⟩, hθ ?_⟩
    rw [hθφ]
    simp
  · rintro ⟨a, rfl⟩
    change θ (φ a) ∈ A
    rw [hθφ]
    exact (ρ a).2

end Lift

end CFSG.RankThree.PartOne.CTP
