module

public import CFSG.RankThree.PartTwo.Sec4.RonanK432RowTools
public import CFSG.RankThree.PartTwo.Sec19.SeitzTrialityTorus2

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanK432

open CFSG.RankThree.PartTwo.Sec11 CFSG.RankThree.PartTwo.Sec19

section Plane


variable {n : ℕ} {X : Type} [Field X] [Finite X] {σ : X ≃+* X}

theorem not_weaklyClosed_of_classX_of_plane (P : D4Par n X σ) {x : C0 σ} (hx : IsClassX σ x)
    (hplane : ∃ x₁ x₂ : C0 σ, IsClassX σ x₁ ∧ IsClassX σ x₂ ∧ x₁ * x₂ = x₂ * x₁ ∧
      x₂ ∉ Subgroup.zpowers x₁) :
    ¬ WeaklyClosed (Subgroup.zpowers x) := by
  obtain ⟨x₁, x₂, h₁, h₂, hc, hn⟩ := hplane
  obtain ⟨h, hh⟩ := classX_conj σ P h₁ hx
  have hy : IsClassX σ (h * x₂ * h⁻¹) := IsClassX.conj_mem σ h₂ h
  obtain ⟨g, hg⟩ := classX_conj σ P hx hy
  refine not_weaklyClosed_of_commute_conj (g := g) ?_ ?_
  · rw [hg, ← hh]
    calc h * x₂ * h⁻¹ * (h * x₁ * h⁻¹) = h * (x₂ * x₁) * h⁻¹ := by group
      _ = h * (x₁ * x₂) * h⁻¹ := by rw [hc]
      _ = h * x₁ * h⁻¹ * (h * x₂ * h⁻¹) := by group
  · rw [hg, ← hh]
    intro hmem
    apply hn
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp hmem
    refine Subgroup.mem_zpowers_iff.mpr ⟨i, ?_⟩
    have h1 : (h * x₁ * h⁻¹) ^ i = h * x₁ ^ i * h⁻¹ := by simp [conj_zpow]
    rw [h1] at hi
    have := congrArg (fun t => h⁻¹ * t * h) hi
    simpa [mul_assoc] using this

end Plane

end CFSG.RankThree.PartTwo.Sec4.RonanK432
