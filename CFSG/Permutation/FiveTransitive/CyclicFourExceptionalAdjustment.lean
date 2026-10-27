module

public import CFSG.Permutation.FiveTransitive.CyclicFourSquareTranslation
public import Mathlib.Data.ZMod.QuotientGroup

public section

namespace CFSG

namespace FiveTransitive.CyclicFourExceptionalAdjustment

open MulAction

theorem adjust_to_fix
    {H Y : Type*} [CommGroup H] [Finite H] [Finite Y] [MulAction H Y]
    (x : H) (hx : orderOf x = 4)
    (hfree : ∀ (q : Subgroup.zpowers x) (t : Y), q • t = t → q = 1)
    (E : Set Y) (hE : E.ncard = 4)
    (hstable : ∀ (g : H) (t : Y), t ∈ E → g • t ∈ E)
    (w : H) (hw : w ^ 2 = 1) :
    ∃ u : H, (u = w ∨ u = x ^ 2 * w) ∧ ∀ t ∈ E, u • t = t := by
  obtain ⟨t, ht⟩ := Set.nonempty_of_ncard_ne_zero (by omega : E.ncard ≠ 0)
  let C := Subgroup.zpowers x
  have hC : Nat.card C = 4 := by rw [Nat.card_zpowers, hx]
  let j : C → E := fun q => ⟨q.val • t, hstable q.val t ht⟩
  have hj : Function.Injective j := by
    intro p q he
    have hpq : p • t = q • t := congrArg Subtype.val he
    have hfix : (q⁻¹ * p) • t = t := by rw [mul_smul, hpq, inv_smul_smul]
    exact (inv_mul_eq_one.mp (hfree _ t hfix)).symm
  have hsur : Function.Surjective j := (hj.bijective_of_nat_card_le (by
    rw [hC, Nat.card_coe_set_eq, hE])).surjective
  have hOE : orbit C t = E := by
    apply Set.Subset.antisymm
    · intro z hz
      obtain ⟨q, rfl⟩ := mem_orbit_iff.mp hz
      exact hstable q.val t ht
    · intro z hz
      obtain ⟨q, hq⟩ := hsur ⟨z, hz⟩
      exact mem_orbit_iff.mpr ⟨q, congrArg Subtype.val hq⟩
  let b : C := ⟨x, Subgroup.mem_zpowers x⟩
  have hb : orderOf b = 4 := (Subgroup.orderOf_coe b).symm.trans hx
  have hcases := CyclicFourSquareTranslation.orbit_action_cases C hC b hb
    (fun q r => Commute.all _ _) w hw (fun q => Commute.all _ _) t (fun q => hfree q t)
    (by rw [hOE]; exact hstable w t ht)
  rcases hcases with h | h
  · exact ⟨w, Or.inl rfl, fun z hz => h z (hOE.symm ▸ hz)⟩
  · refine ⟨x ^ 2 * w, Or.inr rfl, ?_⟩
    intro z hz
    have hh : w • z = x ^ 2 • z := h z (hOE.symm ▸ hz)
    rw [mul_smul, hh, ← mul_smul, ← pow_add, show 2 + 2 = 4 from rfl, ← hx, pow_orderOf_eq_one, one_smul]

end FiveTransitive.CyclicFourExceptionalAdjustment

end CFSG
