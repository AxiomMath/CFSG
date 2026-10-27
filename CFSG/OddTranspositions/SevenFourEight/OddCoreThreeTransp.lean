module

public import CFSG.OddTranspositions.SevenFourEight.ImageThreeTransp
public import CFSG.OddTranspositions.PartThree.SixThreeGlobal

public section

namespace CFSG.OddTranspositions

open CFSG.Timmesfeld.Bridge Asc72 CFSG.Timmesfeld.Connectivity
open CFSG.OddTranspositions.QZ

theorem pow_eq_one_of_conj_inv_of_mem_center {X : Type} [Group X] {K : Subgroup X} [K.Normal]
    {x y : X} (hx : x * x = 1) (hy : y * y = 1) (hodd : Odd (orderOf (x * y))) {j : ℕ}
    (hc : QuotientGroup.mk' K ((x * y) ^ j) ∈ Subgroup.center (X ⧸ K)) :
    (QuotientGroup.mk' K x * QuotientGroup.mk' K y) ^ j = 1 := by
  set z := (x * y) ^ j with hz
  have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx
  have hyi : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy
  have hinv : x * z * x⁻¹ = z⁻¹ := by
    have h1 : x * (x * y) * x⁻¹ = (x * y)⁻¹ := by
      rw [mul_inv_rev, hxi, hyi, ← mul_assoc, hx, one_mul]
    rw [hz, ← conj_pow, h1, inv_pow]
  have hzbar : QuotientGroup.mk' K z * QuotientGroup.mk' K z = 1 := by
    have hcomm := (Subgroup.mem_center_iff.mp hc) (QuotientGroup.mk' K x)
    have h := congrArg (QuotientGroup.mk' K) hinv
    simp only [map_mul, map_inv] at h
    rw [hcomm, mul_inv_cancel_right] at h
    rw [mul_eq_one_iff_eq_inv]
    exact h
  have hzodd : Odd (orderOf (QuotientGroup.mk' K z)) :=
    (hodd.of_dvd_nat (orderOf_pow_dvd (x := x * y) j)).of_dvd_nat
      (orderOf_map_dvd (QuotientGroup.mk' K) ((x * y) ^ j))
  have hz1 := CFSG.Timmesfeld.Bridge.OddTransp.eq_one_of_mul_self_of_odd hzbar hzodd
  rw [← map_mul, ← map_pow]
  exact hz1

variable {G : Type} [Group G] [Finite G] {D : Set G}

theorem threeTransp_DstarH_oddCore
    (hC : HypothesisC D)
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    (hsecond : ∀ u w v : G, IsTriangle D u w v → orderOf (u * v * w) = 4)
    (hnot3 : ¬ ∀ d ∈ D, ∀ e ∈ D, orderOf (d * e) ∈ ({1, 2, 3} : Set ℕ))
    (hmin : SmallerTwoStar (Nat.card G))
    (hK : ¬ CFSG.oddCore ↥(Halpha D hC.alpha) ≤ Subgroup.center ↥(Halpha D hC.alpha)) :
    ∀ x ∈ DstarH hC, ∀ y ∈ DstarH hC,
      orderOf ((x : ↥(Halpha D hC.alpha) ⧸ CFSG.oddCore ↥(Halpha D hC.alpha)) * (y : ↥(Halpha D hC.alpha) ⧸ CFSG.oddCore ↥(Halpha D hC.alpha))) ∈
        ({1, 2, 3} : Set ℕ) := by
  classical
  have hSH : Setup ↥(Halpha D hC.alpha) (DstarH hC) :=
    ⟨DstarH_isClass hC, DstarH_isOddTransp hC, DstarH_closure_eq_top hC⟩
  have hD := DstarH_isOddTransp hC
  rcases PartThree.sixThree hSH with h1 | h2 | h3
  · exact h1
  swap
  · exact absurd h3 hK
  intro x hx y hy
  have hx2 := hD.mul_self_eq_one hx
  have hy2 := hD.mul_self_eq_one hy
  by_cases hxy : Commute x y
  ·
    have hsq : ((x : ↥(Halpha D hC.alpha) ⧸ CFSG.oddCore ↥(Halpha D hC.alpha)) *
        (y : ↥(Halpha D hC.alpha) ⧸ CFSG.oddCore ↥(Halpha D hC.alpha))) ^ 2 = 1 := by
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_pow,
        (CFSG.Timmesfeld.commute_iff_mul_sq_eq_one hx2 hy2).mp hxy, QuotientGroup.mk_one]
    rcases (Nat.dvd_prime Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hsq) with h | h
    · rw [h]; exact Set.mem_insert _ _
    · rw [h]; exact Set.mem_insert_of_mem _ (Set.mem_insert _ _)
  have hodd : Odd (orderOf (x * y)) := hD.odd_of_not_commute hx hy hxy
  have hM := threeTransp_imageClass hC hrad hsecond hnot3 hmin _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
  set R := CFSG.solvableRadical ↥(Halpha D hC.alpha) with hR
  set j := orderOf (QuotientGroup.mk' R x * QuotientGroup.mk' R y) with hj
  have hjdvd : j ∣ orderOf (x * y) := by
    rw [hj, ← map_mul]
    exact orderOf_map_dvd _ _
  have hjodd : Odd j := hodd.of_dvd_nat hjdvd
  have hzR : (x * y) ^ j ∈ R := by
    rw [← QuotientGroup.eq_one_iff, ← QuotientGroup.mk'_apply, map_pow, map_mul, hj]
    exact pow_orderOf_eq_one _
  have hzc : QuotientGroup.mk' (CFSG.oddCore ↥(Halpha D hC.alpha)) ((x * y) ^ j) ∈
      Subgroup.center (↥(Halpha D hC.alpha) ⧸ CFSG.oddCore ↥(Halpha D hC.alpha)) :=
    h2 (Subgroup.mem_map_of_mem _ hzR)
  have hpow := pow_eq_one_of_conj_inv_of_mem_center hx2 hy2 hodd hzc
  rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply] at hpow
  have hdvd := orderOf_dvd_of_pow_eq_one hpow
  have hj13 : j = 1 ∨ j = 3 := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hM
    rcases hM with h | h | h
    · exact Or.inl h
    · rw [h] at hjodd
      exact absurd hjodd (by decide)
    · exact Or.inr h
  rcases hj13 with h | h
  · rw [h, Nat.dvd_one] at hdvd
    rw [hdvd]
    exact Set.mem_insert _ _
  · rw [h] at hdvd
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h' | h'
    · rw [h']; exact Set.mem_insert _ _
    · rw [h']; exact Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl)

end CFSG.OddTranspositions

end
