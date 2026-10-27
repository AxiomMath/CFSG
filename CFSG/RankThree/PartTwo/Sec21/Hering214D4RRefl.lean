module

public import Mathlib.Data.ZMod.QuotientGroup
public import Mathlib.Tactic.IntervalCases

public section

namespace CFSG.RankThree.PartTwo.Sec21.Hering214

theorem reflection_shape {E : Type*} [CommGroup E] [Finite E] (hE3 : ∀ e : E, e ^ 3 = 1)
    (hE9 : Nat.card E = 9) (φ : MulAut E) (hφ2 : φ * φ = 1) (hφ1 : φ ≠ 1)
    (ℓ : Subgroup E) (hℓ : Nat.card ℓ = 3) (hφℓ : ∀ l ∈ ℓ, φ l ∈ ℓ)
    (hquot : ∀ e : E, φ e * e⁻¹ ∈ ℓ) :
    (∀ l ∈ ℓ, φ l = l⁻¹) ∧ ∃ e : E, e ∉ ℓ ∧ φ e = e := by
  have hφφ : ∀ x : E, φ (φ x) = x := by
    intro x
    have h := DFunLike.congr_fun hφ2 x
    rwa [MulAut.mul_apply, MulAut.one_apply] at h
  have hx3 : ∀ x : E, x ^ (3 : ℤ) = 1 := fun x => by exact_mod_cast hE3 x
  have hzpow : ∀ (x : E) (k : ℤ), x ^ k = x ^ (k % 3) := by
    intro x k
    conv_lhs => rw [← Int.emod_add_mul_ediv k 3]
    rw [zpow_add, zpow_mul, hx3 x, one_zpow, mul_one]
  obtain ⟨l, hlℓ, hl1⟩ : ∃ l ∈ ℓ, l ≠ 1 := by
    by_contra hcon
    have hbot : ℓ = ⊥ := (Subgroup.eq_bot_iff_forall ℓ).mpr fun x hx =>
      Classical.byContradiction fun hne => hcon ⟨x, hx, hne⟩
    rw [hbot, Subgroup.card_bot] at hℓ
    omega
  obtain ⟨e, he⟩ : ∃ e : E, e ∉ ℓ := by
    by_contra hcon
    have htop : ℓ = ⊤ := (Subgroup.eq_top_iff' ℓ).mpr fun x =>
      Classical.byContradiction fun hx => hcon ⟨x, hx⟩
    rw [htop, Subgroup.card_top] at hℓ
    omega
  have hl3 : l * (l * l) = 1 := by rw [← pow_three]; exact hE3 l
  have hinv : l⁻¹ = l * l := inv_eq_of_mul_eq_one_right hl3
  have hl4 : l * l * (l * l) = l := by rw [mul_assoc, hl3, mul_one]
  have hll : l * l ∈ ℓ := ℓ.mul_mem hlℓ hlℓ
  have hord : orderOf l = 3 := orderOf_eq_prime (hE3 l) hl1
  have hℓl : Subgroup.zpowers l = ℓ := by
    apply Subgroup.eq_of_le_of_card_ge ((Subgroup.zpowers_le).mpr hlℓ)
    exact le_of_eq (by rw [Nat.card_zpowers, hord, hℓ])
  have hmem : ∀ x ∈ ℓ, x = 1 ∨ x = l ∨ x = l * l := by
    intro x hx
    rw [← hℓl, Subgroup.mem_zpowers_iff] at hx
    obtain ⟨k, rfl⟩ := hx
    rw [hzpow l k]
    have hk : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
    rcases hk with hk | hk | hk
    · left
      rw [hk, zpow_zero]
    · right
      left
      rw [hk, zpow_one]
    · right
      right
      rw [hk, zpow_two]
  have hnot : ∀ x ∈ ℓ, e * x ∉ ℓ := by
    intro x hx hex
    apply he
    have h := ℓ.mul_mem hex (ℓ.inv_mem hx)
    rwa [mul_inv_cancel_right] at h
  have hgen : ∀ f : MulAut E, f l = l → f e = e → f = 1 := by
    intro f hfl hfe
    let K : Subgroup E :=
      { carrier := {x | f x = x}
        mul_mem' := fun {a b} ha hb => by
          show f (a * b) = a * b
          have ha' : f a = a := ha
          have hb' : f b = b := hb
          rw [map_mul, ha', hb']
        one_mem' := by
          show f 1 = 1
          exact map_one f
        inv_mem' := fun {a} ha => by
          show f a⁻¹ = a⁻¹
          have ha' : f a = a := ha
          rw [map_inv, ha'] }
    have hK : ∀ x, x ∈ K ↔ f x = x := fun x => Iff.rfl
    have hle : ℓ ≤ K := by
      rw [← hℓl, Subgroup.zpowers_le]
      exact (hK l).mpr hfl
    have heK : e ∈ K := (hK e).mpr hfe
    have hdvd : Nat.card K ∣ Nat.card E := Subgroup.card_subgroup_dvd_card K
    have h3 : Nat.card ℓ ∣ Nat.card K := Subgroup.card_dvd_of_le hle
    rw [hℓ] at h3
    rw [hE9] at hdvd
    have hne : Nat.card K ≠ 3 := by
      intro h
      apply he
      have heq : ℓ = K := Subgroup.eq_of_le_of_card_ge hle (by omega)
      rw [heq]
      exact heK
    have hK9 : Nat.card K = 9 := by
      have hle9 : Nat.card K ≤ 9 := Nat.le_of_dvd (by norm_num) hdvd
      generalize Nat.card K = c at hdvd h3 hne hle9 ⊢
      interval_cases c <;> first | rfl | omega | (norm_num at hdvd)
    have hKtop : K = ⊤ := (Subgroup.card_eq_iff_eq_top K).mp (by rw [hK9, hE9])
    apply MulEquiv.ext
    intro x
    have hx : x ∈ K := by
      rw [hKtop]
      exact Subgroup.mem_top x
    exact (hK x).mp hx
  have hφl_ne1 : φ l ≠ 1 := by
    intro h
    have h' := hφφ l
    rw [h, map_one] at h'
    exact hl1 h'.symm
  have hφl : φ l = l * l := by
    rcases hmem _ (hφℓ l hlℓ) with h | h | h
    · exact absurd h hφl_ne1
    · exfalso
      rcases hmem _ (hquot e) with h' | h' | h'
      · exact hφ1 (hgen φ h (mul_inv_eq_one.mp h'))
      ·
        have hpe := mul_inv_eq_iff_eq_mul.mp h'
        have h2 : l * (l * e) = e := by
          have h0 := hφφ e
          rw [hpe, map_mul, h, hpe] at h0
          exact h0
        have h3 : l * l = 1 := mul_right_cancel (a := l * l) (b := e) (c := 1)
          (by rw [one_mul, mul_assoc]; exact h2)
        apply hl1
        have h4 := hl3
        rw [h3, mul_one] at h4
        exact h4
      ·
        have hpe := mul_inv_eq_iff_eq_mul.mp h'
        have h2 : l * l * (l * l * e) = e := by
          have h0 := hφφ e
          rw [hpe, map_mul, map_mul, h, hpe] at h0
          exact h0
        have h3 : l * e = e := by
          rw [← mul_assoc, hl4] at h2
          exact h2
        apply hl1
        exact mul_right_cancel (a := l) (b := e) (c := 1) (by rw [one_mul]; exact h3)
    · exact h
  refine ⟨?_, ?_⟩
  · intro l' hl'
    rcases hmem l' hl' with h | h | h
    · rw [h, map_one, inv_one]
    · rw [h, hφl, hinv]
    · rw [h, map_mul, hφl, mul_inv, hinv]
  · rcases hmem _ (hquot e) with h | h | h
    · exact ⟨e, he, mul_inv_eq_one.mp h⟩
    ·
      have hpe := mul_inv_eq_iff_eq_mul.mp h
      refine ⟨e * (l * l), hnot _ hll, ?_⟩
      rw [map_mul, map_mul, hφl, hpe, hl4]
      rw [mul_right_comm l e l, mul_comm (l * l) e]
    ·
      have hpe := mul_inv_eq_iff_eq_mul.mp h
      refine ⟨e * l, hnot _ hlℓ, ?_⟩
      rw [map_mul, hφl, hpe]
      rw [mul_right_comm (l * l) e (l * l), hl4]
      exact mul_comm l e

end CFSG.RankThree.PartTwo.Sec21.Hering214
