module

public import CFSG.Certificates.CosetEnumeration
public import Certificates.Data.CFSGNative.CosetTable.Enum

public section

namespace CFSG.CosetTable

open CFSG.Certificates.CosetEnumeration

variable {m : ℕ}

theorem fixes_of_period_one {G : Type*} [Group G] {Ω : Type} (ψ : G →* (Equiv.Perm Ω)ᵐᵒᵖ)
    (b : Ω) {w : G} (h : Function.minimalPeriod (ψ w).unop b = 1) : (ψ w).unop b = b :=
  Function.minimalPeriod_eq_one_iff_isFixedPt.1 h

theorem pow_eq_one_of_fixes {G : Type*} [Group G] {Ω : Type} (ψ : G →* (Equiv.Perm Ω)ᵐᵒᵖ)
    (b : Ω) {z : G} (hz : z ^ 3 = 1) (hper : Function.minimalPeriod (ψ z).unop b = 3) {j : ℕ}
    (hfix : (ψ (z ^ j)).unop b = b) : z ^ j = 1 := by
  have h1 : Function.IsPeriodicPt (ψ z).unop j b := by
    have : (ψ (z ^ j)).unop = (ψ z).unop ^ j := by
      rw [map_pow]; exact MulOpposite.unop_pow _ _
    show ((ψ z).unop)^[j] b = b
    rw [← Equiv.Perm.coe_pow, ← this]
    exact hfix
  have h3 : 3 ∣ j := by
    rw [← hper]; exact h1.minimalPeriod_dvd
  obtain ⟨c, rfl⟩ := h3
  rw [pow_mul, hz, one_pow]

end CFSG.CosetTable
