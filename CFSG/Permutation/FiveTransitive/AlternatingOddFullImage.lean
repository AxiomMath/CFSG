module

public import Mathlib.GroupTheory.SpecificGroups.Alternating

public section

namespace CFSG

namespace FiveTransitive.AlternatingOddFullImage

theorem eq_top {F : Type*} [Fintype F] [DecidableEq F]
    (H : Subgroup (Equiv.Perm F)) (hAlt : alternatingGroup F ≤ H)
    (x : Equiv.Perm F) (hx : x ∈ H) (hodd : x.sign = -1) : H = ⊤ := by
  apply top_unique
  intro σ _
  rcases Int.units_eq_one_or σ.sign with hσ | hσ
  · exact hAlt (Equiv.Perm.mem_alternatingGroup.mpr hσ)
  · have hprod : σ * x⁻¹ ∈ H := by
      apply hAlt
      rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_mul,
        Equiv.Perm.sign_inv, hσ, hodd]
      simp
    simpa only [inv_mul_cancel_right] using H.mul_mem hprod hx

end FiveTransitive.AlternatingOddFullImage

end CFSG
