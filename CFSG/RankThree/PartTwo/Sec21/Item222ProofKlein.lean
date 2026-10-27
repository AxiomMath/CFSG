module

public import CFSG.RankThree.PartTwo.Sec21.Item22Refl
import CFSG.RankThree.PartTwo.Sec13.Item13GL

public section

namespace CFSG.RankThree.PartTwo.Sec21.Item222Proof

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo

variable {P : Type*} [Group P]

theorem inv_mul_inv_eq_self (hP3 : ∀ a : P, a ^ 3 = 1) (w : P) : w⁻¹ * w⁻¹ = w := by
  have h : w * w * w = 1 := by rw [← pow_three', hP3]
  calc w⁻¹ * w⁻¹ = w⁻¹ * w⁻¹ * (w * w * w) := by rw [h, mul_one]
    _ = w := by group

theorem mem_commOf_of_apply_eq_inv (hP3 : ∀ a : P, a ^ 3 = 1) {φ : MulAut P} {w : P}
    (h : φ w = w⁻¹) : w ∈ commOf φ := by
  have e : w⁻¹ * φ w = w := by rw [h, inv_mul_inv_eq_self hP3]
  rw [← e]
  exact mem_commOf φ w

theorem eq_one_of_eq_inv (hP3 : ∀ a : P, a ^ 3 = 1) {w : P} (h : w = w⁻¹) : w = 1 := by
  have h2 : w * w = 1 := by
    calc w * w = w * w⁻¹ := by rw [← h]
      _ = 1 := mul_inv_cancel w
  have h3 : w * w * w = 1 := by rw [← pow_three', hP3]
  rwa [h2, one_mul] at h3

theorem apply_mem_commOf (hP : ∀ a b : P, a * b = b * a) {φ ψ : MulAut P} (hc : φ * ψ = ψ * φ)
    {x : P} (hx : x ∈ commOf φ) : ψ x ∈ commOf φ := by
  rw [← range_commHom hP] at hx ⊢
  obtain ⟨a, rfl⟩ := hx
  refine ⟨ψ a, ?_⟩
  have hψφ : ψ (φ a) = φ (ψ a) := by
    change (ψ * φ) a = (φ * ψ) a
    rw [hc]
  rw [commHom_apply, commHom_apply, map_mul, map_inv, hψφ]

theorem commOf_mul_le (φ ψ : MulAut P) : commOf (φ * ψ) ≤ commOf φ ⊔ commOf ψ := by
  rw [commOf, Subgroup.closure_le]
  rintro _ ⟨a, rfl⟩
  have e : a⁻¹ * (φ * ψ) a = (a⁻¹ * ψ a) * ((ψ a)⁻¹ * φ (ψ a)) := by
    rw [MulAut.mul_apply]
    group
  change a⁻¹ * (φ * ψ) a ∈ (commOf φ ⊔ commOf ψ : Subgroup P)
  rw [e]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_right (mem_commOf ψ a))
    (Subgroup.mem_sup_left (mem_commOf φ (ψ a)))

theorem eq_zpowers_of_card_three (hP3 : ∀ a : P, a ^ 3 = 1) {ℓ : Subgroup P}
    (hℓ : Nat.card ℓ = 3) {z : P} (hz : z ∈ ℓ) (hz1 : z ≠ 1) : ℓ = Subgroup.zpowers z := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Finite ℓ := Nat.finite_of_card_ne_zero (by omega)
  symm
  refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hz) ?_
  rw [hℓ, Nat.card_zpowers, orderOf_eq_prime (hP3 z) hz1]

theorem exists_ne_one_of_card_three {ℓ : Subgroup P} (hℓ : Nat.card ℓ = 3) :
    ∃ z ∈ ℓ, z ≠ 1 := by
  by_contra h
  push Not at h
  have hb : ℓ = ⊥ := (Subgroup.eq_bot_iff_forall ℓ).mpr h
  rw [hb, Subgroup.card_bot] at hℓ
  omega

theorem nine_lt_card_of_klein [Finite P] (hP : ∀ a b : P, a * b = b * a)
    (hP3 : ∀ a : P, a ^ 3 = 1) {v₁ v₂ : MulAut P} (h₁ : orderOf v₁ = 2) (h₂ : orderOf v₂ = 2)
    (hc : v₁ * v₂ = v₂ * v₁) (hne : v₁ ≠ v₂)
    (hk₁ : Nat.card (commOf v₁) = Nat.card (commOf (v₁ * v₂)))
    (hk₂ : Nat.card (commOf v₂) = Nat.card (commOf (v₁ * v₂)))
    {W : Subgroup P} (hW₁ : commOf v₁ ≤ W) (hW₂ : commOf v₂ ≤ W) : 9 < Nat.card W := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_contra hW9
  push Not at hW9
  have hv₁ := apply_apply_of_orderOf_eq_two h₁
  have hv₂ := apply_apply_of_orderOf_eq_two h₂
  have hW₃ : commOf (v₁ * v₂) ≤ W := (commOf_mul_le v₁ v₂).trans (sup_le hW₁ hW₂)
  have hv11 : v₁ * v₁ = 1 := by rw [← pow_two, ← h₁, pow_orderOf_eq_one]
  have hv22 : v₂ * v₂ = 1 := by rw [← pow_two, ← h₂, pow_orderOf_eq_one]
  have h12 : (v₁ * v₂) * (v₁ * v₂) = 1 := by
    calc (v₁ * v₂) * (v₁ * v₂) = v₁ * (v₂ * v₁) * v₂ := by group
      _ = v₁ * (v₁ * v₂) * v₂ := by rw [hc]
      _ = (v₁ * v₁) * (v₂ * v₂) := by group
      _ = 1 := by rw [hv11, hv22, one_mul]
  have h₃ : orderOf (v₁ * v₂) = 2 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    refine orderOf_eq_prime (by rw [pow_two]; exact h12) fun h => hne ?_
    calc v₁ = v₁ * (v₂ * v₂) := by rw [hv22, mul_one]
      _ = (v₁ * v₂) * v₂ := by group
      _ = v₂ := by rw [h, one_mul]
  have hPp : IsPGroup 3 P := fun a => ⟨1, by rw [pow_one, hP3]⟩
  obtain ⟨j, hj⟩ := IsPGroup.iff_card.mp (hPp.to_subgroup W)
  have hj2 : j ≤ 2 := by
    by_contra h
    have : 3 ^ 3 ≤ 3 ^ j := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  set k := Nat.card (commOf v₁) with hkdef
  have hkW : k ∣ Nat.card W := Subgroup.card_dvd_of_le hW₁
  have hk1 : k ≠ 1 := by
    intro h
    have hb : commOf v₁ = ⊥ := Subgroup.card_eq_one.mp h
    rw [(commOf_eq_bot_iff v₁).mp hb, orderOf_one] at h₁
    omega
  have hcard_le : ∀ {X : Subgroup P}, X ≤ W → Nat.card X = Nat.card W → X = W :=
    fun hX h => Subgroup.eq_of_le_of_card_ge hX h.ge
  by_cases hkW' : k = Nat.card W
  ·
    have e₁ : commOf v₁ = W := hcard_le hW₁ hkW'
    have e₂ : commOf v₂ = W := hcard_le hW₂ (by rw [hk₂, ← hk₁, hkW'])
    have e₃ : commOf (v₁ * v₂) = W := hcard_le hW₃ (by rw [← hk₁, hkW'])
    obtain ⟨w, hwW, hw1⟩ : ∃ w ∈ W, w ≠ 1 := by
      by_contra h
      push Not at h
      have hb : W = ⊥ := (Subgroup.eq_bot_iff_forall W).mpr h
      rw [hb, Subgroup.card_bot] at hkW'
      exact hk1 hkW'
    have i₁ : v₁ w = w⁻¹ := inv_of_mem_commOf hP hv₁ (e₁ ▸ hwW)
    have i₂ : v₂ w = w⁻¹ := inv_of_mem_commOf hP hv₂ (e₂ ▸ hwW)
    have i₃ : (v₁ * v₂) w = w⁻¹ :=
      inv_of_mem_commOf hP (apply_apply_of_orderOf_eq_two h₃) (e₃ ▸ hwW)
    have hfix : (v₁ * v₂) w = w := by
      rw [MulAut.mul_apply, i₂, map_inv, i₁, inv_inv]
    exact hw1 (eq_one_of_eq_inv hP3 (hfix.symm.trans i₃))
  ·
    have hk3 : k = 3 := by
      rcases (show j = 0 ∨ j = 1 ∨ j = 2 by omega) with rfl | rfl | rfl
      · rw [pow_zero] at hj
        rw [hj] at hkW
        exact absurd (Nat.dvd_one.mp hkW) hk1
      · rw [pow_one] at hj
        rw [hj] at hkW hkW'
        rcases (Nat.dvd_prime Nat.prime_three).mp hkW with h | h
        · exact absurd h hk1
        · exact absurd h hkW'
      · rw [hj] at hkW hkW'
        obtain ⟨i, hi, hki⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hkW
        interval_cases i
        · rw [pow_zero] at hki
          exact absurd hki hk1
        · rw [pow_one] at hki
          exact hki
        · exact absurd hki hkW'
    have hc₁ : Nat.card (commOf v₁) = 3 := hk3
    have hc₂ : Nat.card (commOf v₂) = 3 := by rw [hk₂, ← hk₁]; exact hk3
    have hc₃ : Nat.card (commOf (v₁ * v₂)) = 3 := by rw [← hk₁]; exact hk3
    by_cases hℓ : commOf v₁ = commOf v₂
    ·
      have hF : fixedSubgroupOf v₁ ≤ fixedSubgroupOf v₂ := by
        intro x hx
        have hx' : v₁ x = x := hx
        set y := x⁻¹ * v₂ x with hy
        have hyℓ : y ∈ commOf v₁ := hℓ ▸ mem_commOf v₂ x
        have hv₂x : v₁ (v₂ x) = v₂ x := by
          change (v₁ * v₂) x = v₂ x
          rw [hc, MulAut.mul_apply, hx']
        have hyF : v₁ y = y := by rw [hy, map_mul, map_inv, hx', hv₂x]
        have hy1 : y = 1 :=
          eq_one_of_eq_inv hP3 (hyF.symm.trans (inv_of_mem_commOf hP hv₁ hyℓ))
        change v₂ x = x
        rw [hy, inv_mul_eq_one] at hy1
        exact hy1.symm
      have hFeq : fixedSubgroupOf v₁ = fixedSubgroupOf v₂ := by
        refine Subgroup.eq_of_le_of_card_ge hF ?_
        have e1 := card_eq_card_fixed_mul_card_commOf hP v₁
        have e2 := card_eq_card_fixed_mul_card_commOf hP v₂
        rw [hc₁] at e1
        rw [hc₂] at e2
        omega
      exact hne (eq_of_fixed_eq_of_commOf_eq hP hP3 h₁ h₂ hFeq hℓ)
    ·
      obtain ⟨z₁, hz₁, hz₁1⟩ := exists_ne_one_of_card_three hc₁
      obtain ⟨z₂, hz₂, hz₂1⟩ := exists_ne_one_of_card_three hc₂
      have hℓ₁ := eq_zpowers_of_card_three hP3 hc₁ hz₁ hz₁1
      have hℓ₂ := eq_zpowers_of_card_three hP3 hc₂ hz₂ hz₂1
      have key : ∀ {φ ψ : MulAut P} {z : P}, orderOf ψ = 2 → φ * ψ = ψ * φ →
          z ∈ commOf φ → z ≠ 1 → Nat.card (commOf φ) = 3 → Nat.card (commOf ψ) = 3 →
          commOf φ ≠ commOf ψ → ψ z = z := by
        intro φ ψ z hψ hφψ hz hz1 hcφ hcψ hne'
        have hzφ := eq_zpowers_of_card_three hP3 hcφ hz hz1
        have hψz : ψ z ∈ commOf φ := apply_mem_commOf hP hφψ hz
        rw [hzφ] at hψz
        rcases Sec13.eq_of_mem_zpowers_of_pow_three (hP3 z) hψz with h | h | h
        · exact absurd ((map_eq_one_iff ψ ψ.injective).mp h) hz1
        · exact h
        · exfalso
          have hz2 : z ^ 2 = z⁻¹ := by
            rw [eq_inv_iff_mul_eq_one, ← pow_succ, hP3]
          rw [hz2] at h
          have hzψ : z ∈ commOf ψ := mem_commOf_of_apply_eq_inv hP3 h
          apply hne'
          refine Subgroup.eq_of_le_of_card_ge ?_ (by rw [hcφ, hcψ])
          rw [hzφ, Subgroup.zpowers_le]
          exact hzψ
      have f₁ : v₂ z₁ = z₁ := key h₂ hc hz₁ hz₁1 hc₁ hc₂ hℓ
      have f₂ : v₁ z₂ = z₂ := key h₁ hc.symm hz₂ hz₂1 hc₂ hc₁ (Ne.symm hℓ)
      have m₁ : z₁ ∈ commOf (v₁ * v₂) := by
        apply mem_commOf_of_apply_eq_inv hP3
        rw [MulAut.mul_apply, f₁]
        exact inv_of_mem_commOf hP hv₁ hz₁
      have m₂ : z₂ ∈ commOf (v₁ * v₂) := by
        apply mem_commOf_of_apply_eq_inv hP3
        rw [MulAut.mul_apply, inv_of_mem_commOf hP hv₂ hz₂, map_inv, f₂]
      have h₃ := eq_zpowers_of_card_three hP3 hc₃ m₁ hz₁1
      apply hℓ
      rw [hℓ₁, hℓ₂, ← eq_zpowers_of_card_three hP3 hc₃ m₂ hz₂1, ← h₃]

end CFSG.RankThree.PartTwo.Sec21.Item222Proof
