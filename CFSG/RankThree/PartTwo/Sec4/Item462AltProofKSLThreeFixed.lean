module

public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.RankThree.PartTwo.Sec4.Item462AltProof.KSLThree

theorem fixed_of_isPGroup_two {S : Type} [Group S]
    (hZ : ∀ z ∈ Subgroup.center S, z ^ 3 = 1) (β' : MulAut S) {P : Subgroup S}
    (hP : IsPGroup 2 P) (hD : ∀ p ∈ P, (β' p)⁻¹ * p ∈ Subgroup.center S) :
    ∀ p ∈ P, β' p = p := by
  intro p hp
  have hmul : ∀ x y : S, (β' x)⁻¹ * x ∈ Subgroup.center S →
      (β' (x * y))⁻¹ * (x * y) = ((β' x)⁻¹ * x) * ((β' y)⁻¹ * y) := by
    intro x y hx
    have hc := Subgroup.mem_center_iff.mp hx ((β' y)⁻¹)
    calc (β' (x * y))⁻¹ * (x * y) = (β' y)⁻¹ * ((β' x)⁻¹ * x) * y := by
          rw [map_mul]; group
      _ = ((β' x)⁻¹ * x) * (β' y)⁻¹ * y := by rw [hc, mul_assoc]
      _ = ((β' x)⁻¹ * x) * ((β' y)⁻¹ * y) := by rw [mul_assoc]
  have hz := hD p hp
  have hpow : ∀ k : ℕ, (β' (p ^ k))⁻¹ * p ^ k = ((β' p)⁻¹ * p) ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ', hmul p (p ^ k) hz, ih, pow_succ']
  obtain ⟨k, hk⟩ := hP ⟨p, hp⟩
  have hk' : p ^ 2 ^ k = 1 := by
    have := congrArg Subtype.val hk
    simpa using this
  have h1 : ((β' p)⁻¹ * p) ^ 2 ^ k = 1 := by
    rw [← hpow, hk']
    simp
  have h3 : ((β' p)⁻¹ * p) ^ 3 = 1 := hZ _ hz
  have hcop : Nat.Coprime (2 ^ k) 3 := Nat.Coprime.pow_left k (by norm_num)
  have h4 : ((β' p)⁻¹ * p) ^ (Nat.gcd (2 ^ k) 3) = 1 :=
    pow_gcd_eq_one.mpr ⟨h1, h3⟩
  rw [hcop, pow_one] at h4
  exact inv_mul_eq_one.mp h4

theorem fixed_center_of_cube {S : Type} [Group S] (hZ : Nat.card (Subgroup.center S) = 3)
    {β' : MulAut S} (hβ' : β' ^ 3 = 1) : ∀ z ∈ Subgroup.center S, β' z = z := by
  intro z hz
  by_cases hz1 : z = 1
  · rw [hz1, map_one]
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Finite (Subgroup.center S) := Nat.finite_of_card_ne_zero (by rw [hZ]; norm_num)
  have hz3 : z ^ 3 = 1 := by
    have h : (⟨z, hz⟩ : Subgroup.center S) ^ Nat.card (Subgroup.center S) = 1 :=
      pow_card_eq_one'
    rw [hZ] at h
    exact congrArg Subtype.val h
  have ho : orderOf z = 3 := orderOf_eq_prime hz3 hz1
  have hβz : β' z ∈ Subgroup.center S := by
    rw [Subgroup.mem_center_iff]
    intro c
    obtain ⟨d, rfl⟩ := β'.surjective c
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hz d]
  have hcyc : Subgroup.zpowers z = Subgroup.center S :=
    Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hz) (by rw [Nat.card_zpowers, ho, hZ])
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hcyc ▸ hβz)
  have hmod : z ^ (k % 3) = β' z := by
    have h := zpow_mod_orderOf z k
    rw [ho] at h
    push_cast at h
    rw [h, hk]
  have h3 : β' (β' (β' z)) = z := by
    have := congrArg (fun γ : MulAut S => γ z) hβ'
    simpa [pow_three] using this
  rcases (by omega : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2) with h | h | h
  · rw [h, zpow_zero] at hmod
    exact absurd (β'.injective (by rw [← hmod, map_one])) hz1
  · rw [h, zpow_one] at hmod
    exact hmod.symm
  · rw [h] at hmod
    have h2 : β' z = z ^ 2 := by rw [← hmod]; simp
    have h4 : β' (β' z) = z := by
      rw [h2, map_pow, h2, ← pow_mul]
      calc z ^ (2 * 2) = z ^ 3 * z := by rw [show 2 * 2 = 3 + 1 from rfl, pow_succ]
        _ = z := by rw [hz3, one_mul]
    rw [h4, h2] at h3
    exfalso
    apply hz1
    have : z ^ 2 = z := h3
    calc z = z ^ 2 * z⁻¹ := by group
      _ = 1 := by rw [this]; group

end CFSG.RankThree.PartTwo.Sec4.Item462AltProof.KSLThree

end
