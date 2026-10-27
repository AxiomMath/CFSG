module

public import CFSG.Timmesfeld.Closure.MinCex
public import CFSG.Timmesfeld.Moufang.Exceptional

public section

namespace CFSG.Timmesfeld.Bridge

open CFSG.Timmesfeld CFSG.Timmesfeld.Connectivity

variable {G : Type*} [Group G] {D : Set G}

@[expose] def IsInvolutionSet (D : Set G) : Prop := ∀ d ∈ D, orderOf d = 2

namespace IsInvolutionSet

variable {d : G}

theorem orderOf_eq_two (hD : IsInvolutionSet D) (hd : d ∈ D) : orderOf d = 2 := hD d hd

theorem mul_self_eq_one (hD : IsInvolutionSet D) (hd : d ∈ D) : d * d = 1 := by
  rw [← pow_two, ← hD.orderOf_eq_two hd, pow_orderOf_eq_one]

theorem inv_eq (hD : IsInvolutionSet D) (hd : d ∈ D) : d⁻¹ = d :=
  inv_eq_of_mul_eq_one_right (hD.mul_self_eq_one hd)

theorem ne_one (hD : IsInvolutionSet D) (hd : d ∈ D) : d ≠ 1 := by
  rintro rfl
  have h := hD.orderOf_eq_two hd
  rw [orderOf_one] at h
  exact absurd h (by decide)

end IsInvolutionSet

theorem IsRootInvolutionSet.isInvolutionSet (hD : IsRootInvolutionSet D) : IsInvolutionSet D :=
  fun _ hd => hD.orderOf_eq_two hd

theorem isInvolutionSet_image {Q : Type*} [Group Q] (hD : IsInvolutionSet D) (φ : G →* Q)
    (hφ : ∀ x ∈ D, φ x ≠ 1) : IsInvolutionSet (φ '' D) := by
  rintro _ ⟨x, hx, rfl⟩
  exact orderOf_eq_prime (by rw [← map_pow, pow_two, hD.mul_self_eq_one hx, map_one]) (hφ x hx)

@[expose] def OddAcross (D : Set G) : Prop :=
  ∀ x ∈ D, ∀ y ∈ D, ¬ Reach D x y → Odd (orderOf (x * y))

theorem oddAcross_of_isRootInvolutionSet (hD : IsRootInvolutionSet D) : OddAcross D :=
  fun _ hx _ hy h => (opposite_of_not_reach hD hx hy h).2

section Closed

variable (hN : IsNormalSet D) (hD : IsInvolutionSet D)
include hN hD

theorem pow_mul_mem {x y : G} (hx : x ∈ D) (hy : y ∈ D) (n : ℕ) : (x * y) ^ n * x ∈ D := by
  have hxi := hD.inv_eq hx
  have hyi := hD.inv_eq hy
  induction n using Nat.twoStepInduction with
  | zero => simpa using hx
  | one =>
    have := hN x y hy
    rwa [hxi, ← pow_one (x * y)] at this
  | more n ih _ =>
    have := hN (x * y) _ ih
    have hc : x * y * (x * y) ^ n = (x * y) ^ n * (x * y) := (Commute.self_pow (x * y) n).eq
    have e : x * y * ((x * y) ^ n * x) * (x * y)⁻¹ = (x * y) ^ (n + 2) * x := by
      rw [mul_inv_rev, hxi, hyi, pow_add, pow_two]
      calc x * y * ((x * y) ^ n * x) * (y * x) = (x * y * (x * y) ^ n) * (x * y * x) := by
            simp only [mul_assoc]
        _ = (x * y) ^ n * (x * y) * (x * y * x) := by rw [hc]
        _ = (x * y) ^ n * (x * y * (x * y)) * x := by simp only [mul_assoc]
    rwa [e] at this

theorem pow_half_mem (hnp : Moufang.NoPolar D) {x y : G} (hx : x ∈ D) (hy : y ∈ D) {k : ℕ}
    (hk : orderOf (x * y) = k + k) (hk0 : k ≠ 0) : (x * y) ^ k ∈ D := by
  set v := (x * y) ^ k with hv
  have hv1 : v ≠ 1 := pow_ne_one_of_lt_orderOf hk0 (by omega)
  have hvv : v * v = 1 := by rw [hv, ← pow_add, ← hk, pow_orderOf_eq_one]
  have hxv : x * v = v * x := by
    have h := mul_zpow_mul_eq_zpow_neg_mul (hD.mul_self_eq_one hx) (hD.mul_self_eq_one hy)
      (k : ℤ)
    rw [zpow_neg, zpow_natCast, ← hv, inv_eq_of_mul_eq_one_right hvv] at h
    exact h
  have hw : v * x ∈ D := pow_mul_mem hN hD hx hy k
  have hne : x ≠ v * x := fun h => hv1 (by
    have := congrArg (· * x⁻¹) h
    simpa using this.symm)
  have hcomm : Commute x (v * x) := by
    show x * (v * x) = v * x * x
    rw [← mul_assoc, hxv]
  have := hnp x hx (v * x) hw hcomm hne
  rwa [← mul_assoc, hxv, mul_assoc, hD.mul_self_eq_one hx, mul_one] at this

theorem oddAcross_of_noPolar [Finite G] (hnp : Moufang.NoPolar D) : OddAcross D := by
  intro x hx y hy hxy
  by_contra hodd
  obtain ⟨k, hk⟩ := Nat.not_odd_iff_even.1 hodd
  have hk0 : k ≠ 0 := by
    rintro rfl
    have := orderOf_pos (x * y)
    omega
  have hvD := pow_half_mem hN hD hnp hx hy hk hk0
  set v := (x * y) ^ k with hv
  have hvv : v * v = 1 := by rw [hv, ← pow_add, ← hk, pow_orderOf_eq_one]
  have hxv : Commute x v := by
    have h := mul_zpow_mul_eq_zpow_neg_mul (hD.mul_self_eq_one hx) (hD.mul_self_eq_one hy)
      (k : ℤ)
    rw [zpow_neg, zpow_natCast, ← hv, inv_eq_of_mul_eq_one_right hvv] at h
    exact h
  have hvy : Commute v y := by
    have h1 : Commute v (x * y) := (Commute.self_pow (x * y) k).symm
    have h2 : Commute v (x * (x * y)) := hxv.symm.mul_right h1
    rwa [← mul_assoc, hD.mul_self_eq_one hx, one_mul] at h2
  exact hxy (reach_trans (reach_of_commute hx hvD hxv) (reach_of_commute hvD hy hvy))

end Closed

section Odd

variable (hN : IsNormalSet D) (hD : IsInvolutionSet D) (hodd : OddAcross D)
include hD hodd

theorem reach_of_mem_compStab_of_odd {x y : G} (hx : x ∈ D) (hy : y ∈ D)
    (hyS : y ∈ compStab hN x) : Reach D x y := by
  by_contra h
  obtain ⟨g, hg, hgx⟩ := exists_conj_of_odd_orderOf_mul (hD.mul_self_eq_one hx)
    (hD.mul_self_eq_one hy) (hodd x hx y hy h)
  have hle : Subgroup.closure ({x, y} : Set G) ≤ compStab hN x := by
    rw [Subgroup.closure_le]
    rintro z (rfl | rfl)
    · exact mem_compStab_self hN z
    · exact hyS
  have := hle hg
  rw [mem_compStab_iff, hgx] at this
  exact h this

omit hN in
theorem isConj_of_disconnected_of_odd (hdisc : Disconnected D) {x y : G} (hx : x ∈ D)
    (hy : y ∈ D) : IsConj x y := by
  have key : ∀ {a b : G}, a ∈ D → b ∈ D → ¬ Reach D a b → IsConj a b := by
    intro a b ha hb hab
    obtain ⟨g, -, hg⟩ := exists_conj_of_odd_orderOf_mul (hD.mul_self_eq_one ha)
      (hD.mul_self_eq_one hb) (hodd a ha b hb hab)
    exact isConj_iff.2 ⟨g, hg⟩
  by_cases hxy : Reach D x y
  · obtain ⟨z, hz, hxz⟩ := exists_not_reach hdisc (x := x)
    have hyz : ¬ Reach D y z := fun h => hxz (reach_trans hxy h)
    exact (key hx hz hxz).trans (key hy hz hyz).symm
  · exact key hx hy hxy

theorem compStab_ne_top_of_odd (hdisc : Disconnected D) {d : G} (hd : d ∈ D) :
    compStab hN d ≠ ⊤ := by
  intro htop
  obtain ⟨z, hz, hdz⟩ := exists_not_reach hdisc (x := d)
  exact hdz (reach_of_mem_compStab_of_odd hN hD hodd hd hz (by rw [htop]; trivial))

end Odd

end CFSG.Timmesfeld.Bridge
