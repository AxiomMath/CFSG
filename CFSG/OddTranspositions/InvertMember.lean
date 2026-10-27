module

public import CFSG.OddTranspositions.SixThreeLocal

public section

namespace CFSG.OddTranspositions

section InvertMember

variable {G : Type} [Group G] {D : Set G} {u x : G}

theorem mul_mem_of_inverts (hDinv : ∀ g y : G, y ∈ D → g * y * g⁻¹ ∈ D) (hu : u ∈ D)
    (hu2 : u * u = 1) (hxodd : Odd (orderOf x)) (hx : u * x * u = x⁻¹) :
    u * x ∈ D := by
  obtain ⟨j, hj⟩ := hxodd
  have hconjpow : ∀ k : ℕ, u * x ^ k * u = (x ^ k)⁻¹ := by
    intro k
    have hu_inv : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu2
    calc u * x ^ k * u = u * x ^ k * u⁻¹ := by rw [hu_inv]
      _ = (u * x * u⁻¹) ^ k := by rw [conj_pow]
      _ = (u * x * u) ^ k := by rw [hu_inv]
      _ = (x⁻¹) ^ k := by rw [hx]
      _ = (x ^ k)⁻¹ := inv_pow x k
  have hpow : ∀ k : ℕ, x ^ k * u = u * (x ^ k)⁻¹ := by
    intro k
    have := congrArg (fun z => u * z) (hconjpow k)
    simpa only [← mul_assoc, hu2, one_mul] using this
  have h2 : x ^ (2 * j + 1) = 1 := by
    rw [← hj]
    exact pow_orderOf_eq_one x
  have hsq : x ^ j * x ^ j = x⁻¹ := by
    rw [← pow_add, ← two_mul]
    apply eq_inv_of_mul_eq_one_left
    rw [← pow_succ]
    exact h2
  have hinv : (x ^ j)⁻¹ * (x ^ j)⁻¹ = x := by
    rw [← mul_inv_rev, hsq, inv_inv]
  have hconj : x ^ j * u * (x ^ j)⁻¹ = u * x := by
    rw [hpow j, mul_assoc, hinv]
  exact hconj ▸ hDinv (x ^ j) u hu

end InvertMember

section SecondKind

open CFSG.Timmesfeld CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72

variable {G : Type} [Group G] [Finite G] {D : Set G}

theorem normal_le_center_of_secondKindTriangle' (hS : Asc72.Setup G D)
    {u w v : G} (htri : IsTriangle D u w v) (h4 : orderOf (u * v * w) = 4)
    (hno : ∀ x ∈ D, x ∈ Subgroup.closure {u, w} → IsTriangle D u x v →
      ¬ IsThirdKind u x v)
    (hm : 3 < orderOf (u * w))
    {N : Subgroup G} (hN : N.Normal) (hNo : Odd (Nat.card N)) :
    N ≤ Subgroup.center G := by
  refine normal_le_center_of_secondKindTriangle hS htri h4 hno hm hN hNo ?_
  intro x hxN _ hxinv
  exact mul_mem_of_inverts
    (fun g y hy => CFSG.Timmesfeld.conj_mem_of_isClass hS.isClass g hy)
    htri.1 (hS.oddT.mul_self_eq_one htri.1)
    (hNo.of_dvd_nat (Subgroup.orderOf_dvd_natCard N hxN)) hxinv

theorem normal_le_center_of_mem_closure_commSet' (hS : Asc72.Setup G D)
    {N : Subgroup G} (hN : N.Normal) (hNo : Odd (Nat.card N))
    {u : G} (hu : u ∈ D) (huD : u ∈ Subgroup.closure (commSet D u)) :
    N ≤ Subgroup.center G := by
  refine normal_le_center_of_mem_closure_commSet hS hN hNo hu huD ?_
  intro x hx hx1 hinv
  exact mul_mem_of_inverts
    (fun g y hy => CFSG.Timmesfeld.conj_mem_of_isClass hS.isClass g hy) hu
    (hS.oddT.mul_self_eq_one hu) (hNo.of_dvd_nat (Subgroup.orderOf_dvd_natCard N hx)) hinv


end SecondKind

end CFSG.OddTranspositions
