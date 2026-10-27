module

public import CFSG.Quasithin.EmptyFaithful.S1417Natural
public import Mathlib.Tactic.Polynomial.Basic

public section

namespace CFSG.Quasithin.H13.A6

open CFSG.Quasithin

namespace A6L74

variable {Γ : Type*} [Group Γ]

theorem eq_or_of_mem_zpowers_three {z y : Γ} (hz : z ^ 3 = 1) (hy : y ∈ Subgroup.zpowers z) :
    y = 1 ∨ y = z ∨ y = z⁻¹ := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  have h3 : z ^ (3 : ℤ) = 1 := by
    rw [show (3 : ℤ) = ((3 : ℕ) : ℤ) by norm_num, zpow_natCast, hz]
  have hk : z ^ k = z ^ (k % 3) := by
    conv_lhs => rw [← Int.emod_add_mul_ediv k 3]
    rw [zpow_add, zpow_mul, h3, one_zpow, mul_one]
  rw [hk]
  obtain h | h | h : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
  · left
    rw [h, zpow_zero]
  · right; left
    rw [h, zpow_one]
  · right; right
    rw [h, eq_inv_iff_mul_eq_one, ← zpow_add_one]
    rw [show (2 : ℤ) + 1 = 3 by norm_num, h3]

theorem conj_eq_of_mem_zpowers {σ z : Γ} (hσ : σ ^ 3 = 1) (hz : z ^ 3 = 1) (hz1 : z ≠ 1)
    (h : σ * z * σ⁻¹ ∈ Subgroup.zpowers z) : σ * z * σ⁻¹ = z := by
  rcases eq_or_of_mem_zpowers_three hz h with h1 | h1 | h1
  · exfalso
    apply hz1
    have e : z = σ⁻¹ * (σ * z * σ⁻¹) * σ := by group
    rw [e, h1]
    group
  · exact h1
  · exfalso
    have h2 : σ * (σ * (σ * z * σ⁻¹) * σ⁻¹) * σ⁻¹ = z⁻¹ := by
      have e2 : σ * z⁻¹ * σ⁻¹ = (σ * z * σ⁻¹)⁻¹ := by group
      rw [h1, e2, h1, inv_inv, h1]
    have e : σ * (σ * (σ * z * σ⁻¹) * σ⁻¹) * σ⁻¹ = (σ * σ * σ) * z * (σ * σ * σ)⁻¹ := by
      simp only [mul_assoc, mul_inv_rev]
    rw [e, ← pow_three', hσ, one_mul, inv_one, mul_one, eq_inv_iff_mul_eq_one] at h2
    apply hz1
    calc z = z ^ 3 * (z * z)⁻¹ := by group
      _ = 1 := by rw [hz, h2, inv_one, one_mul]

theorem sup_zpowers_eq_of_card [Finite Γ] {K : Subgroup Γ} (hK : Nat.card K = 9) {a b : Γ}
    (ha : a ∈ K) (hb : b ∈ K) (ha3 : a ^ 3 = 1) (ha1 : a ≠ 1) (hba : b ∉ Subgroup.zpowers a) :
    Subgroup.zpowers a ⊔ Subgroup.zpowers b = K := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hBK : Subgroup.zpowers a ⊔ Subgroup.zpowers b ≤ K :=
    sup_le ((Subgroup.zpowers_le).2 ha) ((Subgroup.zpowers_le).2 hb)
  have hza : Nat.card (Subgroup.zpowers a) = 3 := by
    rw [Nat.card_zpowers, orderOf_eq_prime ha3 ha1]
  have h1 : 3 ∣ Nat.card ↥(Subgroup.zpowers a ⊔ Subgroup.zpowers b) :=
    hza ▸ Subgroup.card_dvd_of_le le_sup_left
  have h2 : Nat.card ↥(Subgroup.zpowers a ⊔ Subgroup.zpowers b) ∣ 3 ^ 2 := by
    have := Subgroup.card_dvd_of_le hBK
    rw [hK] at this
    norm_num
    exact this
  have h3 : Nat.card ↥(Subgroup.zpowers a ⊔ Subgroup.zpowers b) ≠ 3 := by
    intro h
    have e : Subgroup.zpowers a = Subgroup.zpowers a ⊔ Subgroup.zpowers b :=
      Subgroup.eq_of_le_of_card_ge le_sup_left (by rw [h, hza])
    exact hba (e ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers b))
  obtain ⟨m, hm, hm'⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 h2
  refine Subgroup.eq_of_le_of_card_ge hBK ?_
  rw [hK]
  interval_cases m
  · rw [pow_zero] at hm'
    rw [hm'] at h1
    norm_num at h1
  · rw [pow_one] at hm'
    exact absurd hm' h3
  · rw [hm']
    norm_num

theorem SL2_exists_three : ∃ x : S1417.SL2, x ^ 3 = 1 ∧ x ≠ 1 := by decide

theorem SL2_exists_two : ∃ t : S1417.SL2, t ^ 2 = 1 ∧ t ≠ 1 := by decide

theorem SL2_cube : ∀ y x : S1417.SL2, y ^ 3 = 1 → x ^ 3 = 1 → x ≠ 1 →
    y = 1 ∨ y = x ∨ y = x⁻¹ := by decide

theorem SL2_inv_conj : ∀ t u x : S1417.SL2,
    (t ^ 2 = 1 ∧ t ≠ 1 ∧ u ^ 2 = 1 ∧ u ≠ 1 ∧ x ^ 3 = 1 ∧ x ≠ 1) →
      u = t ∨ u = x * t * x⁻¹ ∨ u = x⁻¹ * t * x := by decide

theorem SL2_gen : ∀ t x y : S1417.SL2, t ^ 2 = 1 → t ≠ 1 → x ^ 3 = 1 → x ≠ 1 →
    y = 1 ∨ y = x ∨ y = x⁻¹ ∨ y = t ∨ y = x * t ∨ y = x⁻¹ * t := by decide

theorem exists_three_of_equiv {K L : Subgroup Γ} (e : ↥L ≃* S1417.SL2)
    (hK3 : ∀ k ∈ K, k ^ 3 = 1) (hLK : ∀ y ∈ L, y ^ 3 = 1 → y ∈ K) :
    ∃ d ∈ L, d ∈ K ∧ d ^ 3 = 1 ∧ d ≠ 1 ∧ ∀ y ∈ L, y ∈ K → y = 1 ∨ y = d ∨ y = d⁻¹ := by
  obtain ⟨x, hx3, hx1⟩ := SL2_exists_three
  have hd3 : ((e.symm x : ↥L) : Γ) ^ 3 = 1 := by
    have h : (e.symm x) ^ 3 = 1 := by rw [← map_pow, hx3, map_one]
    simpa using congrArg Subtype.val h
  have hd1 : ((e.symm x : ↥L) : Γ) ≠ 1 := by
    intro h
    apply hx1
    have h' : e.symm x = 1 := Subtype.ext h
    simpa using congrArg e h'
  refine ⟨(e.symm x : Γ), (e.symm x).2, hLK _ (e.symm x).2 hd3, hd3, hd1, fun y hy hyK => ?_⟩
  have hy3 : (⟨y, hy⟩ : ↥L) ^ 3 = 1 := Subtype.ext (by simpa using hK3 y hyK)
  rcases SL2_cube (e ⟨y, hy⟩) x (by rw [← map_pow, hy3, map_one]) hx3 hx1 with h | h | h
  · left
    have h' : (⟨y, hy⟩ : ↥L) = 1 := e.injective (by rw [h, map_one])
    simpa using congrArg Subtype.val h'
  · right; left
    have h' : (⟨y, hy⟩ : ↥L) = e.symm x := e.injective (by rw [h, e.apply_symm_apply])
    simpa using congrArg Subtype.val h'
  · right; right
    have h' : (⟨y, hy⟩ : ↥L) = (e.symm x)⁻¹ := e.injective (by rw [h, map_inv, e.apply_symm_apply])
    simpa using congrArg Subtype.val h'

end A6L74

end CFSG.Quasithin.H13.A6
