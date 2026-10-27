module

public import CFSG.RankThree.PartTwo.Sec4.Item47Inputs

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanK429

open CFSG CFSG.RankThree.PartTwo.Sec4

private theorem int_modEq_one_of_cube {k : ℤ} (h : Int.ModEq 3 (k * (k * k)) 1) :
    Int.ModEq 3 k 1 := by
  unfold Int.ModEq at h ⊢
  rw [Int.mul_emod, Int.mul_emod k k 3] at h
  have hr : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
  rcases hr with hr | hr | hr <;> rw [hr] at h <;> omega

theorem center_le_autFix_of_card_three {X : Type*} [Group X]
    (h3 : Nat.card (Subgroup.center X) = 3) {α : MulAut X} (hα3 : α ^ 3 = 1) :
    Subgroup.center X ≤ autFix α := by
  have hcube : ∀ x : X, α (α (α x)) = x := by
    intro x
    have h := congrArg (fun φ : MulAut X => φ x) hα3
    simpa [pow_three', MulAut.mul_apply, MulAut.one_apply] using h
  intro z hz
  rw [mem_autFix]
  by_cases hz1 : z = 1
  · rw [hz1]
    exact map_one α
  have hαz : α z ∈ Subgroup.center X := by
    rw [Subgroup.mem_center_iff]
    intro g
    have hc := Subgroup.mem_center_iff.mp hz (α (α g))
    have h' := congrArg (⇑α) hc
    simp only [map_mul, hcube] at h'
    exact h'
  haveI : Finite (Subgroup.center X) := Nat.finite_of_card_ne_zero (by omega)
  have hord_dvd : orderOf z ∣ 3 := by
    have h := orderOf_dvd_natCard (⟨z, hz⟩ : Subgroup.center X)
    rw [h3, Subgroup.orderOf_mk] at h
    exact h
  have hord1 : orderOf z ≠ 1 := fun h => hz1 (orderOf_eq_one_iff.mp h)
  have hord3 : orderOf z = 3 :=
    ((Nat.dvd_prime Nat.prime_three).mp hord_dvd).resolve_left hord1
  have hzp : Subgroup.zpowers z = Subgroup.center X :=
    Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hz)
      (by rw [Nat.card_zpowers, hord3]; omega)
  have hαz' : α z ∈ Subgroup.zpowers z := by
    rw [hzp]
    exact hαz
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hαz'
  have hpow : ∀ n : ℤ, α (z ^ n) = z ^ (k * n) := by
    intro n
    rw [map_zpow, ← hk, ← zpow_mul]
  have h3z : α (α (α z)) = z ^ (k * (k * k)) := by
    rw [← hk, hpow, hpow]
  have hcz : z ^ (k * (k * k)) = z ^ (1 : ℤ) := by
    rw [zpow_one, ← h3z, hcube z]
  have hmod : Int.ModEq 3 (k * (k * k)) 1 := by
    have h := zpow_eq_zpow_iff_modEq.mp hcz
    rw [hord3] at h
    exact_mod_cast h
  have hk1 : Int.ModEq 3 k 1 := int_modEq_one_of_cube hmod
  have hzk : z ^ k = z ^ (1 : ℤ) := by
    rw [zpow_eq_zpow_iff_modEq, hord3]
    exact_mod_cast hk1
  rw [zpow_one] at hzk
  rw [← hk]
  exact hzk

end CFSG.RankThree.PartTwo.Sec4.RonanK429
