module

public import CFSG.Quasithin.Vol2.Asc94.HeJ2

public section

namespace CFSG.Quasithin.A94.HeJ

open Matrix

theorem gl2_conj_pow_three : ∀ g x : GL2, x ^ 3 = 1 → g * x * g⁻¹ = x ∨ g * x * g⁻¹ = x⁻¹ := by
  decide +kernel

theorem gl2_order_three_fpf : ∀ g : GL2, g ^ 3 = 1 → g ≠ 1 → ∀ v : V2, g.val *ᵥ v = v → v = 0 := by
  decide +kernel

theorem gl2_cent_card : ∀ g : GL2, g ^ 3 = 1 → g ≠ 1 →
    (Finset.univ.filter fun M : M2 => g.val * M = M * g.val).card = 4 := by
  decide +kernel

theorem card_isUnit_M2 : Nat.card {M : M2 // IsUnit M} = 6 := by
  rw [← card_GL2]
  exact Nat.card_congr ⟨fun p => p.2.unit, fun u => ⟨u.val, u.isUnit⟩, fun p => Subtype.ext rfl,
    fun u => Units.ext rfl⟩

end CFSG.Quasithin.A94.HeJ
