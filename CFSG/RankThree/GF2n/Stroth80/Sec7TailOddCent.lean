module

public import CFSG.RankThree.GF2n.Stroth80.Sec7TailTIConfig
public import CFSG.RankThree.GF2n.Stroth80.Sec7TailOddNormal

public section

namespace CFSG.RankThree.GF2n.Stroth80

open Subgroup

theorem eq_one_of_mem_odd_of_mem_pGroup_two {X : Type*} [Group X] {O N : Subgroup X}
    (hOodd : Odd (Nat.card O)) (hN2 : IsPGroup 2 N) {x : X} (hxO : x ∈ O) (hxN : x ∈ N) :
    x = 1 := by
  have hO : x ^ Nat.card O = 1 := by
    have h := congrArg Subtype.val (pow_card_eq_one' (G := ↥O) (x := ⟨x, hxO⟩))
    rw [Subgroup.coe_pow, Subgroup.coe_one] at h
    exact h
  obtain ⟨j, hj⟩ := IsPGroup.exists_pow_pow_eq_one hN2 (⟨x, hxN⟩ : ↥N)
  have hN : x ^ 2 ^ j = 1 := by
    have h := congrArg Subtype.val hj
    rw [Subgroup.coe_pow, Subgroup.coe_one] at h
    exact h
  have hcop : Nat.Coprime (2 ^ j) (Nat.card O) :=
    Nat.Coprime.pow_left j (Nat.coprime_two_left.mpr hOodd)
  exact (pow_eq_one_iff_of_coprime hcop).mp ⟨hN, hO⟩

theorem odd_normal_eq_bot_of_cent {X : Type*} [Group X] [Finite X] {H V N O : Subgroup X}
    (hVH : V ≤ H) (hV2 : ∀ x ∈ V, x ^ 2 = 1) (hVab : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x)
    (hV4 : 4 ≤ Nat.card V)
    (hti : ∀ g : X, ∀ x ∈ V, x ≠ 1 → g * x * g⁻¹ ∈ V → g ∈ normalizer (V : Set X))
    (hNK : N ≤ NormIn H V) (hNn : ∀ k ∈ NormIn H V, k ∈ normalizer (N : Set X))
    (hN2 : IsPGroup 2 N) (hcent : ∀ k ∈ NormIn H V, (∀ n ∈ N, k * n = n * k) → k ∈ N)
    (hOH : ∀ h ∈ H, h ∈ normalizer (O : Set X)) (hOle : O ≤ H) (hOodd : Odd (Nat.card O)) :
    O = ⊥ := by
  refine odd_normal_eq_bot hVH hV2 hVab hV4 hti hOH hOle hOodd ?_
  intro k hkO hkV
  have hkK : k ∈ NormIn H V := mem_NormIn.mpr ⟨hOle hkO, hkV⟩
  have hcomm : ∀ n ∈ N, k * n = n * k := by
    intro n hn
    have hnH : n ∈ H := (mem_NormIn.mp (hNK hn)).1
    have hnO : n ∈ normalizer (O : Set X) := hOH n hnH
    have h1 : k * n * k⁻¹ ∈ N := (Subgroup.mem_set_normalizer_iff.mp (hNn k hkK) n).mp hn
    have h2 : n * k⁻¹ * n⁻¹ ∈ O :=
      (Subgroup.mem_set_normalizer_iff.mp hnO k⁻¹).mp (O.inv_mem hkO)
    have hc1 : k * (n * k⁻¹ * n⁻¹) ∈ O := O.mul_mem hkO h2
    have hc2 : k * (n * k⁻¹ * n⁻¹) ∈ N := by
      have e : k * (n * k⁻¹ * n⁻¹) = k * n * k⁻¹ * n⁻¹ := by simp only [mul_assoc]
      rw [e]
      exact N.mul_mem h1 (N.inv_mem hn)
    have hc := eq_one_of_mem_odd_of_mem_pGroup_two hOodd hN2 hc1 hc2
    have h4 : k * n * k⁻¹ * n⁻¹ = 1 := by simpa only [mul_assoc] using hc
    exact mul_inv_eq_iff_eq_mul.mp (mul_inv_eq_one.mp h4)
  have hkN : k ∈ N := hcent k hkK hcomm
  exact eq_one_of_mem_odd_of_mem_pGroup_two hOodd hN2 hkO hkN

end CFSG.RankThree.GF2n.Stroth80
