module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Quasithin.Background.F3Dihedral
public import CFSG.Quasithin.Background.F7Basic

public section

namespace CFSG.Quasithin.H13.F431.L3

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Open

theorem fix_of_lines {P : Type} [Group P] {F : Type} [Field F] {Z B₀ : Subgroup P} (ξ ζ : F → P)
    (hZ : ∀ x, x ∈ Z ↔ ∃ c, x = ζ c)
    (hinj : ∀ a c a' c', ξ a * ζ c = ξ a' * ζ c' → a = a' ∧ c = c')
    (hξ0 : ξ 0 = 1) (hζ0 : ζ 0 = 1)
    {t : P} (ht : t ∈ B₀) {χ ψ : F} (hχψ : χ ≠ ψ) (hχ : ∀ a, t * ξ a * t⁻¹ = ξ (χ * a))
    (hψ : ∀ c, t * ζ c * t⁻¹ = ζ (ψ * c)) {s : P} (hs : ∀ c, s * ζ c * s⁻¹ = ξ c)
    {m : P} {α β : F} (hαβ : α ≠ 0 ∨ β ≠ 0)
    (hm : ∀ c, m * ζ c * m⁻¹ = ξ (α * c) * ζ (β * c))
    (hstab : ∀ t' ∈ B₀, ∀ z ∈ conjSub m Z, t' * z * t'⁻¹ ∈ conjSub m Z) :
    conjSub m Z = Z ∨ conjSub m Z = conjSub s Z := by
  have hmem : ∀ z, z ∈ conjSub m Z ↔ ∃ c, z = ξ (α * c) * ζ (β * c) := by
    intro z
    rw [mem_conjSub, hZ]
    constructor
    · rintro ⟨c, hc⟩
      refine ⟨c, ?_⟩
      rw [← hm, ← hc]
      group
    · rintro ⟨c, hc⟩
      refine ⟨c, ?_⟩
      rw [hc, ← hm]
      group
  have hsmem : ∀ z, z ∈ conjSub s Z ↔ ∃ c, z = ξ c := by
    intro z
    rw [mem_conjSub, hZ]
    constructor
    · rintro ⟨c, hc⟩
      refine ⟨c, ?_⟩
      rw [← hs, ← hc]
      group
    · rintro ⟨c, hc⟩
      refine ⟨c, ?_⟩
      rw [hc, ← hs]
      group
  have hz₀ : ξ (α * 1) * ζ (β * 1) ∈ conjSub m Z := (hmem _).mpr ⟨1, rfl⟩
  have h1 := hstab t ht _ hz₀
  have hconj : t * (ξ (α * 1) * ζ (β * 1)) * t⁻¹ = ξ (χ * (α * 1)) * ζ (ψ * (β * 1)) := by
    rw [← hχ, ← hψ]
    group
  rw [hconj, hmem] at h1
  obtain ⟨c', hc'⟩ := h1
  obtain ⟨e1, e2⟩ := hinj _ _ _ _ hc'
  have hα0 : α = 0 ∨ β = 0 := by
    by_contra hcon
    have hα : α ≠ 0 := fun h => hcon (Or.inl h)
    have hβ : β ≠ 0 := fun h => hcon (Or.inr h)
    apply hχψ
    have h3 : χ = c' := by
      have : α * (χ - c') = 0 := by linear_combination e1
      exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left hα)
    have h4 : ψ = c' := by
      have : β * (ψ - c') = 0 := by linear_combination e2
      exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left hβ)
    rw [h3, h4]
  rcases hα0 with hα | hβ
  · left
    have hβ : β ≠ 0 := hαβ.resolve_left (by simp [hα])
    ext z
    rw [hmem, hZ]
    constructor
    · rintro ⟨c, hc⟩
      exact ⟨β * c, by rw [hc, hα, zero_mul, hξ0, one_mul]⟩
    · rintro ⟨c, hc⟩
      exact ⟨β⁻¹ * c, by
        rw [hc, hα, zero_mul, hξ0, one_mul, ← mul_assoc, mul_inv_cancel₀ hβ, one_mul]⟩
  · right
    have hα : α ≠ 0 := hαβ.resolve_right (by simp [hβ])
    ext z
    rw [hmem, hsmem]
    constructor
    · rintro ⟨c, hc⟩
      exact ⟨α * c, by rw [hc, hβ, zero_mul, hζ0, mul_one]⟩
    · rintro ⟨c, hc⟩
      exact ⟨α⁻¹ * c, by
        rw [hc, hβ, zero_mul, hζ0, mul_one, ← mul_assoc, mul_inv_cancel₀ hα, one_mul]⟩

end CFSG.Quasithin.H13.F431.L3
