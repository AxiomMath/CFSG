module

public import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic.Group

public section

namespace CFSG.RankThree.PartOne.KF1322

theorem pow_three_of_inverted {G : Type*} [Group G] {D : Set G} {H : Subgroup G}
    (hDconj : ∀ x ∈ H, ∀ g ∈ D, x * g * x⁻¹ ∈ D)
    (hodd : ∀ s ∈ D, ∀ t ∈ D, Odd (orderOf (s * t)) → orderOf (s * t) = 1 ∨ orderOf (s * t) = 3)
    {t : G} (ht : t ∈ D) (htt : t * t = 1) {x : G} (hx : x ∈ H) (hinv : t * x * t = x⁻¹)
    (hxodd : Odd (orderOf x)) : x ^ 3 = 1 := by
  have hs : x * t * x⁻¹ ∈ D := hDconj x hx t ht
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  have h0 : t * x⁻¹ * t = x := by
    have h := congrArg (fun z => z⁻¹) hinv
    simp only [mul_inv_rev, htinv, inv_inv] at h
    rw [mul_assoc]
    exact h
  have hprod : (x * t * x⁻¹) * t = x ^ 2 := by
    calc (x * t * x⁻¹) * t = x * (t * x⁻¹ * t) := by group
      _ = x * x := by rw [h0]
      _ = x ^ 2 := (sq x).symm
  have hcop : Nat.Coprime (orderOf x) 2 := Nat.coprime_two_right.mpr hxodd
  have h2 : orderOf (x ^ 2) = orderOf x := hcop.orderOf_pow
  have h3 := hodd _ hs _ ht (by rw [hprod, h2]; exact hxodd)
  rw [hprod, h2] at h3
  rcases h3 with h | h
  · have : x = 1 := orderOf_eq_one_iff.mp h
    rw [this, one_pow]
  · rw [← h]
    exact pow_orderOf_eq_one x

end CFSG.RankThree.PartOne.KF1322
