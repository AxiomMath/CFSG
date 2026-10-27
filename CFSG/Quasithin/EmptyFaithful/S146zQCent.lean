module

public import Mathlib.Tactic.Group
public import Mathlib.Algebra.Group.Subgroup.Defs

public section

namespace CFSG.Quasithin

section QCent

variable {G : Type} [Group G]

theorem qcent_of_trans {P R N Zs Qs : Subgroup G}
    (hNab : ∀ a ∈ N, ∀ a' ∈ N, a * a' = a' * a) (hZN : Zs ≤ N)
    (hPZ : ∀ x ∈ P, ∀ z ∈ Zs, x * z * x⁻¹ = z)
    (hRZ : ∀ h ∈ R, ∀ z ∈ Zs, h * z * h⁻¹ = z)
    (hPN : ∀ x ∈ P, ∀ a ∈ N, x * a * x⁻¹ * a⁻¹ ∈ Zs)
    (hRN : ∀ h ∈ R, ∀ a ∈ N, h * a * h⁻¹ ∈ N)
    (hRP : ∀ h ∈ R, ∀ x ∈ P, h * x * h⁻¹ * x⁻¹ ∈ Qs)
    (hQN : ∀ q ∈ Qs, ∀ a ∈ N, q * a * q⁻¹ = a)
    (htr : ∀ a ∈ N, a ∉ Zs → ∀ a' ∈ N, a' ∉ Zs → ∃ h ∈ R, ∃ z ∈ Zs, h * a * h⁻¹ = a' * z)
    (hrich : ∃ a ∈ N, ∃ a' ∈ N, a ∉ Zs ∧ a' ∉ Zs ∧ a * a' ∉ Zs) :
    ∀ x ∈ P, ∀ a ∈ N, x * a * x⁻¹ = a := by
  intro x hx
  have hhom : ∀ a ∈ N, ∀ a' ∈ N, x * (a * a') * x⁻¹ * (a * a')⁻¹ =
      (x * a * x⁻¹ * a⁻¹) * (x * a' * x⁻¹ * a'⁻¹) := by
    intro a ha a' ha'
    have h1 : x * a' * x⁻¹ * a'⁻¹ ∈ N := hZN (hPN x hx a' ha')
    have hc : a * (x * a' * x⁻¹ * a'⁻¹) = (x * a' * x⁻¹ * a'⁻¹) * a := hNab _ ha _ h1
    have e1 : x * (a * a') * x⁻¹ * (a * a')⁻¹ =
        (x * a * x⁻¹ * a⁻¹) * (a * (x * a' * x⁻¹ * a'⁻¹) * a⁻¹) := by group
    have e2 : a * (x * a' * x⁻¹ * a'⁻¹) * a⁻¹ = x * a' * x⁻¹ * a'⁻¹ := by
      rw [hc]; group
    rw [e1, e2]
  have hinv : ∀ h ∈ R, ∀ a ∈ N,
      x * (h * a * h⁻¹) * x⁻¹ * (h * a * h⁻¹)⁻¹ = x * a * x⁻¹ * a⁻¹ := by
    intro h hh a ha
    have hh' : h⁻¹ ∈ R := R.inv_mem hh
    have ha'' : h * a * h⁻¹ ∈ N := hRN h hh a ha
    have hZ'' : x * (h * a * h⁻¹) * x⁻¹ * (h * a * h⁻¹)⁻¹ ∈ Zs := hPN x hx _ ha''
    have hcen := hRZ h⁻¹ hh' _ hZ''
    rw [inv_inv] at hcen
    have hq : h⁻¹ * x * h * x⁻¹ ∈ Qs := by
      have := hRP h⁻¹ hh' x hx
      rwa [inv_inv] at this
    have hxa : x * a * x⁻¹ ∈ N := by
      have e : x * a * x⁻¹ = (x * a * x⁻¹ * a⁻¹) * a := by group
      rw [e]
      exact N.mul_mem (hZN (hPN x hx a ha)) ha
    have hq1 := hQN _ hq _ hxa
    have key : h⁻¹ * (x * (h * a * h⁻¹) * x⁻¹ * (h * a * h⁻¹)⁻¹) * h =
        (h⁻¹ * x * h * x⁻¹) * (x * a * x⁻¹) * (h⁻¹ * x * h * x⁻¹)⁻¹ * a⁻¹ := by group
    rw [hcen, hq1] at key
    exact key
  have hZone : ∀ z ∈ Zs, x * z * x⁻¹ * z⁻¹ = 1 := fun z hz => by
    rw [hPZ x hx z hz]; group
  obtain ⟨a₀, ha₀, a₁, ha₁, ha₀Z, ha₁Z, ha₀₁Z⟩ := hrich
  have hconst : ∀ a ∈ N, a ∉ Zs →
      x * a * x⁻¹ * a⁻¹ = x * a₀ * x⁻¹ * a₀⁻¹ := by
    intro a ha haZ
    obtain ⟨h, hh, z, hz, hhaz⟩ := htr a ha haZ a₀ ha₀ ha₀Z
    have h1 := hinv h hh a ha
    rw [hhaz] at h1
    rw [← h1, hhom a₀ ha₀ z (hZN hz), hZone z hz, mul_one]
  have hs : x * a₀ * x⁻¹ * a₀⁻¹ = 1 := by
    have h1 := hhom a₀ ha₀ a₁ ha₁
    rw [hconst _ (N.mul_mem ha₀ ha₁) ha₀₁Z, hconst a₁ ha₁ ha₁Z] at h1
    have h2 : (x * a₀ * x⁻¹ * a₀⁻¹) * (x * a₀ * x⁻¹ * a₀⁻¹) =
        (x * a₀ * x⁻¹ * a₀⁻¹) * 1 := by rw [mul_one]; exact h1.symm
    exact mul_left_cancel h2
  intro a ha
  by_cases haZ : a ∈ Zs
  · exact hPZ x hx a haZ
  · have := hconst a ha haZ
    rw [hs] at this
    exact mul_inv_eq_one.mp this

end QCent

end CFSG.Quasithin
