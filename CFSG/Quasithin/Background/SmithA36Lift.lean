module

public import CFSG.LieType.Steinberg.CentralExt.SLCentrallyClosed

public section

namespace CFSG.Quasithin.SmithA36

open Matrix CFSG.LieType.Steinberg.CentralExt
open scoped commutatorElement

section InvolutionLift

variable {E G : Type*} [Group E] [Group G] {π : E →* G}

theorem eq_one_of_sq_eq_one_of_odd {z : E} (hz : z ^ 2 = 1) (hodd : Odd (orderOf z)) : z = 1 := by
  by_contra h
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [orderOf_eq_prime hz h] at hodd
  exact Nat.not_odd_iff_even.mpr even_two hodd

theorem exists_lift_sq_eq_one (hodd : ∀ z ∈ π.ker, Odd (orderOf z)) {y : E} (hy : π y ^ 2 = 1) :
    ∃ x : E, π x = π y ∧ x ^ 2 = 1 := by
  have hw : y ^ 2 ∈ π.ker := by rw [MonoidHom.mem_ker, map_pow, hy]
  obtain ⟨k, hk⟩ := hodd _ hw
  refine ⟨y ^ (2 * k + 1), ?_, ?_⟩
  · rw [map_pow, pow_succ, pow_mul, hy, one_pow, one_mul]
  · rw [← pow_mul, show (2 * k + 1) * 2 = 2 * (2 * k + 1) by ring, pow_mul, ← hk,
      pow_orderOf_eq_one]

variable (hcen : π.ker ≤ Subgroup.center E) (hodd : ∀ z ∈ π.ker, Odd (orderOf z))
include hcen hodd

theorem eq_of_sq_eq_one {x y : E} (hx : x ^ 2 = 1) (hy : y ^ 2 = 1) (h : π x = π y) : x = y := by
  have hz : x⁻¹ * y ∈ π.ker := by rw [MonoidHom.mem_ker, map_mul, map_inv, h, inv_mul_cancel]
  have hc : Commute x (x⁻¹ * y) := Subgroup.mem_center_iff.1 (hcen hz) x
  have hsq : (x⁻¹ * y) ^ 2 = 1 := by
    have h2 := hy
    rw [← mul_inv_cancel_left x y, hc.mul_pow, hx, one_mul] at h2
    exact h2
  rw [← inv_mul_eq_one]
  exact eq_one_of_sq_eq_one_of_odd hsq (hodd _ hz)

theorem commute_of_sq_eq_one {x y : E} (hy : y ^ 2 = 1) (h : π x * π y = π y * π x) :
    x * y = y * x := by
  have hz : ⁅x, y⁆ ∈ π.ker := by
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact h
  have hc : Commute ⁅x, y⁆ y := (Subgroup.mem_center_iff.1 (hcen hz) y).symm
  have hxy : x * y * x⁻¹ = ⁅x, y⁆ * y := by rw [commutatorElement_def, inv_mul_cancel_right]
  have hsq : ⁅x, y⁆ ^ 2 = 1 := by
    have h2 : (x * y * x⁻¹) ^ 2 = 1 := by rw [conj_pow, hy, mul_one, mul_inv_cancel]
    rw [hxy, hc.mul_pow, hy, mul_one] at h2
    exact h2
  rw [← commutatorElement_eq_one_iff_mul_comm]
  exact eq_one_of_sq_eq_one_of_odd hsq (hodd _ hz)

theorem commutatorElement_eq_of_sq_eq_one {a b c : E} (ha : a ^ 2 = 1) (hc : c ^ 2 = 1)
    (hac : a * c = c * a) (h : π ⁅a, b⁆ = π c) : ⁅a, b⁆ = c := by
  obtain ⟨z, hz, hab⟩ : ∃ z ∈ π.ker, ⁅a, b⁆ = c * z :=
    ⟨c⁻¹ * ⁅a, b⁆, by rw [MonoidHom.mem_ker, map_mul, map_inv, h, inv_mul_cancel],
      (mul_inv_cancel_left c _).symm⟩
  have hzc := Subgroup.mem_center_iff.1 (hcen hz)
  have haa : a * a = 1 := by rw [← sq]; exact ha
  have hainv : a⁻¹ = a := inv_eq_of_mul_eq_one_right haa
  have hinv : a * ⁅a, b⁆ * a⁻¹ = ⁅a, b⁆⁻¹ := by
    have e1 : a * ⁅a, b⁆ * a⁻¹ = a * a * b * a⁻¹ * b⁻¹ * a⁻¹ := by
      rw [commutatorElement_def]
      group
    have e2 : ⁅a, b⁆⁻¹ = b * a * b⁻¹ * a⁻¹ := by
      rw [commutatorElement_def]
      group
    rw [e1, e2, haa, one_mul, hainv]
  have hfix : a * (c * z) * a⁻¹ = c * z := by
    rw [mul_inv_eq_iff_eq_mul, ← mul_assoc, hac, mul_assoc, hzc a, mul_assoc]
  rw [hab, hfix] at hinv
  have h2 : (c * z) ^ 2 = 1 := by
    rw [sq]
    exact mul_eq_one_iff_eq_inv.mpr hinv
  have hcomm : Commute c z := hzc c
  rw [hcomm.mul_pow, hc, one_mul] at h2
  rw [hab, eq_one_of_sq_eq_one_of_odd h2 (hodd _ hz), mul_one]

end InvolutionLift

theorem injective_of_section {E G : Type*} [Group E] [Group G] [Group.IsPerfect E] {π : E →* G}
    (hcen : π.ker ≤ Subgroup.center E) {σ : G →* E} (hσ : ∀ g, π (σ g) = g) :
    Function.Injective π := by
  have hle : commutator E ≤ σ.range := by
    rw [commutator_def, Subgroup.commutator_le]
    intro x _ y _
    rw [TorusLift.commutatorElement_eq_of_map_eq hcen (hσ (π x)).symm (hσ (π y)).symm,
      ← map_commutatorElement]
    exact ⟨_, rfl⟩
  have hsurj : ∀ x : E, ∃ g, σ g = x := fun x =>
    hle (by rw [Group.IsPerfect.commutator_eq_top]; trivial)
  intro x y hxy
  obtain ⟨a, rfl⟩ := hsurj x
  obtain ⟨b, rfl⟩ := hsurj y
  rw [hσ, hσ] at hxy
  rw [hxy]

section SpecialLinear

variable {m : ℕ} {F : Type} [Field F]

theorem tv_sq_eq_one [CharP F 2] (i j : Fin (m + 1)) (s : F) : SLClosed.tv F i j s ^ 2 = 1 := by
  by_cases h : i = j
  · subst h
    simp [SLClosed.tv]
  · rw [sq, ← SLClosed.tv_add h, CharTwo.add_self_eq_zero, SLClosed.tv_of_ne h,
      SpecialLinearGroup.transvection_coeff_zero]

theorem sl_exists_section_of_charTwo [Finite F] [CharP F 2] (hm : 2 ≤ m) {E : Type*} [Group E]
    {π : E →* SpecialLinearGroup (Fin (m + 1)) F} (hπ : Function.Surjective π)
    (hcen : π.ker ≤ Subgroup.center E) (hodd : ∀ z ∈ π.ker, Odd (orderOf z)) :
    ∃ σ : SpecialLinearGroup (Fin (m + 1)) F →* E, ∀ g, π (σ g) = g := by
  have hex : ∀ (i j : Fin (m + 1)) (s : F), ∃ x : E, π x = SLClosed.tv F i j s ∧ x ^ 2 = 1 := by
    intro i j s
    obtain ⟨y, hy⟩ := hπ (SLClosed.tv F i j s)
    obtain ⟨x, hx, hx2⟩ :=
      exists_lift_sq_eq_one hodd (y := y) (by rw [hy]; exact tv_sq_eq_one i j s)
    exact ⟨x, hx.trans hy, hx2⟩
  choose Y hYπ hY2 using hex
  have hcomm : ∀ i j k l : Fin (m + 1), i ≠ j → k ≠ l → j ≠ k → l ≠ i → ∀ s t,
      Y i j s * Y k l t = Y k l t * Y i j s := fun i j k l hij hkl hjk hli s t =>
    commute_of_sq_eq_one hcen hodd (hY2 k l t) (by
      rw [hYπ, hYπ]
      exact SLClosed.tv_commute hij hkl hjk hli s t)
  refine SLClosed.exists_section_of_lifts Y (fun i j hij s t => ?_) hcomm
    (fun i j l hij hjl hil s t => ?_) (fun i j _ s => hYπ i j s) hm
  ·
    have hc : Commute (Y i j s) (Y i j t) := hcomm i j i j hij hij hij.symm hij.symm s t
    refine eq_of_sq_eq_one hcen hodd (hY2 i j (s + t)) ?_ ?_
    · rw [hc.mul_pow, hY2, hY2, one_mul]
    · rw [map_mul, hYπ, hYπ, hYπ, SLClosed.tv_add hij]
  ·
    refine commutatorElement_eq_of_sq_eq_one hcen hodd (hY2 i j s) (hY2 i l _)
      (hcomm i j i l hij hil hij.symm hil.symm s _) ?_
    rw [map_commutatorElement, hYπ, hYπ, hYπ, SLClosed.tv_chain hij hjl hil, one_mul]

theorem injective_of_perfect_sl_charTwo [Finite F] [CharP F 2] (hm : 2 ≤ m) {E : Type*} [Group E]
    [Group.IsPerfect E] {π : E →* SpecialLinearGroup (Fin (m + 1)) F}
    (hπ : Function.Surjective π) (hcen : π.ker ≤ Subgroup.center E)
    (hodd : ∀ z ∈ π.ker, Odd (orderOf z)) : Function.Injective π := by
  obtain ⟨σ, hσ⟩ := sl_exists_section_of_charTwo hm hπ hcen hodd
  exact injective_of_section hcen hσ

end SpecialLinear

end CFSG.Quasithin.SmithA36
