module

public import CFSG.RankThree.Native.FiveLocalAction
public import CFSG.RankThree.Native.FiveLocalPCoreChecks

public section

namespace CFSG.RankThree.Native.FiveLocal

open Subgroup CFSG.Monster.B.Pinned
open scoped Matrix

variable {G : Type*} [Group G]

@[expose] def i0Elt (x h : G) : Fin 5 → G :=
  ![x, h * x * h⁻¹, h ^ 2 * x * (h ^ 2)⁻¹, h ^ 3 * x * (h ^ 3)⁻¹, h ^ 4]

namespace Rel

variable [Finite G] {x h z : G} {q : Fin 4 → G} (hR : Rel x h q z)
include hR

theorem A_pow {g : G} (hg : g ∈ K x h q) (n : ℕ) : A q z (g ^ n) = A q z g ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, hR.A_one]
  | succ n ih => rw [pow_succ, pow_succ, hR.A_mul (pow_mem hg n) hg, ih]

theorem A_h_inv : A q z h⁻¹ = f5H ^ 7 := by
  have e : f5H * A q z h⁻¹ = 1 := by
    rw [← hR.A_h, ← hR.A_mul h_mem_K (inv_mem h_mem_K), mul_inv_cancel, hR.A_one]
  calc A q z h⁻¹ = f5H ^ 7 * f5H * A q z h⁻¹ := by rw [f5H_pow_seven_mul, one_mul]
    _ = f5H ^ 7 := by rw [mul_assoc, e, mul_one]

theorem A_x_inv : A q z x⁻¹ = f5X ^ 4 := by
  have e : f5X * A q z x⁻¹ = 1 := by
    rw [← hR.A_x, ← hR.A_mul x_mem_K (inv_mem x_mem_K), mul_inv_cancel, hR.A_one]
  calc A q z x⁻¹ = f5X ^ 4 * f5X * A q z x⁻¹ := by rw [f5X_pow_four_mul, one_mul]
    _ = f5X ^ 4 := by rw [mul_assoc, e, mul_one]

omit [Finite G] in
private theorem conj_pow_h_z (n : ℕ) : (h ^ n)⁻¹ * z * h ^ n = z ^ 2 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc (h ^ (n + 1))⁻¹ * z * h ^ (n + 1) = h⁻¹ * ((h ^ n)⁻¹ * z * h ^ n) * h := by group
      _ = (h⁻¹ * z * h) ^ 2 ^ n := by rw [ih, conj_pow']
      _ = z ^ 2 ^ (n + 1) := by rw [hR.conj_hz, ← pow_mul, pow_succ, mul_comm]

omit hR [Finite G] in
private theorem conj_comm_z {c y : G} {m : ℕ} (hy : y * z = z * y) (hc : c⁻¹ * z * c = z ^ m) :
    c * y * c⁻¹ * z = z * (c * y * c⁻¹) := by
  have h1 : Commute (c * y * c⁻¹) (c * z ^ m * c⁻¹) :=
    (Commute.conj_iff c).2 (Commute.pow_right (hy : Commute y z) m)
  have h2 : c * z ^ m * c⁻¹ = z := by
    rw [← hc]
    group
  rw [h2] at h1
  exact h1

theorem i0Elt_mem_H0 (k : Fin 5) : i0Elt x h k ∈ H0 x h q := by
  have hxz : x * z = z * x := by
    calc x * z = x * (x⁻¹ * z * x) := by rw [hR.conj_xz]
      _ = z * x := by group
  have hK (n : ℕ) : h ^ n * x * (h ^ n)⁻¹ ∈ K x h q :=
    mul_mem (mul_mem (pow_mem h_mem_K n) x_mem_K) (inv_mem (pow_mem h_mem_K n))
  have hC (n : ℕ) := conj_comm_z hxz (hR.conj_pow_h_z n)
  rw [hR.mem_H0]
  fin_cases k
  · exact ⟨x_mem_K, hxz⟩
  · show h * x * h⁻¹ ∈ K x h q ∧ h * x * h⁻¹ * z = z * (h * x * h⁻¹)
    have h1 := And.intro (hK 1) (hC 1)
    simp only [pow_one] at h1
    exact h1
  · exact ⟨hK 2, hC 2⟩
  · exact ⟨hK 3, hC 3⟩
  · refine ⟨pow_mem h_mem_K 4, ?_⟩
    have h4 : (h ^ 4)⁻¹ * z * h ^ 4 = z := by
      rw [hR.conj_pow_h_z 4, show (2 : ℕ) ^ 4 = 5 * 3 + 1 by norm_num, pow_succ, pow_mul,
        hR.z_pow_five, one_pow, one_mul]
    show h ^ 4 * z = z * h ^ 4
    calc h ^ 4 * z = h ^ 4 * ((h ^ 4)⁻¹ * z * h ^ 4) := by rw [h4]
      _ = z * h ^ 4 := by group

theorem A_i0Elt (k : Fin 5) : A q z (i0Elt x h k) = f5I0Mat k := by
  have hinv (n : ℕ) : A q z (h ^ n)⁻¹ = (f5H ^ 7) ^ n := by
    rw [← inv_pow, hR.A_pow (inv_mem h_mem_K), hR.A_h_inv]
  have hconj (n : ℕ) : A q z (h ^ n * x * (h ^ n)⁻¹) = f5H ^ n * f5X * (f5H ^ 7) ^ n := by
    rw [hR.A_mul (mul_mem (pow_mem h_mem_K n) x_mem_K) (inv_mem (pow_mem h_mem_K n)),
      hR.A_mul (pow_mem h_mem_K n) x_mem_K, hR.A_pow h_mem_K, hR.A_h, hR.A_x, hinv]
  fin_cases k
  · exact hR.A_x
  · show A q z (h * x * h⁻¹) = f5H * f5X * f5H ^ 7
    have h1 := hconj 1
    simp only [pow_one] at h1
    exact h1
  · exact hconj 2
  · exact hconj 3
  · show A q z (h ^ 4) = f5H ^ 4
    rw [hR.A_pow h_mem_K, hR.A_h]

theorem A_conj_i0Elt_one {u : G} (hu : u ∈ K x h q) :
    A q z ((i0Elt x h 1)⁻¹ * u * i0Elt x h 1) =
      f5H * f5X ^ 4 * f5H ^ 7 * A q z u * (f5H * f5X * f5H ^ 7) := by
  have hy : i0Elt x h 1 = h * x * h⁻¹ := rfl
  have hyK : h * x * h⁻¹ ∈ K x h q := mul_mem (mul_mem h_mem_K x_mem_K) (inv_mem h_mem_K)
  have hyiK : h * x⁻¹ * h⁻¹ ∈ K x h q :=
    mul_mem (mul_mem h_mem_K (inv_mem x_mem_K)) (inv_mem h_mem_K)
  have hyinv : (h * x * h⁻¹)⁻¹ = h * x⁻¹ * h⁻¹ := by group
  have hAy : A q z (h * x * h⁻¹) = f5H * f5X * f5H ^ 7 := by
    rw [hR.A_mul (mul_mem h_mem_K x_mem_K) (inv_mem h_mem_K), hR.A_mul h_mem_K x_mem_K,
      hR.A_h, hR.A_x, hR.A_h_inv]
  have hAyi : A q z (h * x⁻¹ * h⁻¹) = f5H * f5X ^ 4 * f5H ^ 7 := by
    rw [hR.A_mul (mul_mem h_mem_K (inv_mem x_mem_K)) (inv_mem h_mem_K),
      hR.A_mul h_mem_K (inv_mem x_mem_K), hR.A_h, hR.A_x_inv, hR.A_h_inv]
  rw [hy, hyinv, hR.A_mul (mul_mem hyiK hu) hyK, hR.A_mul hyiK hu, hAyi, hAy]

theorem exists_A_eq_pow_of_mem_P {u : G} (hu : u ∈ P x q) : ∃ j < 5, A q z u = f5X ^ j := by
  classical
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  let T : Subgroup G := ((zpowers f5XU).comap hR.AU).map (K x h q).subtype
  have hQT : Q q ≤ T := fun g hg => Subgroup.mem_map.2
    ⟨⟨g, Q_le_K hg⟩, Subgroup.mem_comap.2 (by rw [hR.AU_of_mem_Q hg]; exact one_mem _), rfl⟩
  have hxT : x ∈ T := Subgroup.mem_map.2
    ⟨⟨x, x_mem_K⟩, Subgroup.mem_comap.2 (by rw [hR.AU_x]; exact mem_zpowers _), rfl⟩
  obtain ⟨g, hg, rfl⟩ := (sup_le hQT (zpowers_le.2 hxT) : P x q ≤ T) hu
  have hord : orderOf f5XU = 5 := orderOf_eq_prime f5XU_pow_five f5XU_ne_one
  have hmem := (mem_zpowers_iff_mem_range_orderOf (x := f5XU)).1 (Subgroup.mem_comap.1 hg)
  rw [hord, Finset.mem_image] at hmem
  obtain ⟨j, hj, hgj⟩ := hmem
  refine ⟨j, Finset.mem_range.1 hj, ?_⟩
  rw [Subgroup.coe_subtype, ← hR.AU_val g, ← hgj, Units.val_pow_eq_pow_val, f5XU_val]

theorem mem_Q_of_mem_P_of_A_eq_one {u : G} (hu : u ∈ P x q) (hA : A q z u = 1) : u ∈ Q q := by
  let P₁ : Subgroup G := P x q ⊓ hR.AU.ker.map (K x h q).subtype
  have hQP₁ : Q q ≤ P₁ := fun g hg =>
    ⟨le_sup_left (a := Q q) hg, ⟨⟨g, Q_le_K hg⟩, hR.AU_of_mem_Q hg, rfl⟩⟩
  have hxP₁ : x ∉ P₁ := by
    rintro ⟨-, ⟨g, hg, hgx⟩⟩
    obtain rfl : g = ⟨x, x_mem_K⟩ := Subtype.ext hgx
    exact f5XU_ne_one (hR.AU_x ▸ (MonoidHom.mem_ker.1 hg))
  have hdvd : Nat.card P₁ ∣ 5 ^ 6 := hR.card_P ▸ Subgroup.card_dvd_of_le inf_le_left
  obtain ⟨k, hk, hcard⟩ := (Nat.dvd_prime_pow (by norm_num : Nat.Prime 5)).1 hdvd
  have hQdvd : 5 ^ 5 ∣ 5 ^ k := hcard ▸ hR.card_Q ▸ Subgroup.card_dvd_of_le hQP₁
  have hk5 : 5 ≤ k := (Nat.pow_dvd_pow_iff_le_right (by norm_num)).1 hQdvd
  have hk' : k = 5 := by
    by_contra hne
    have hk6 : k = 6 := by omega
    have hPeq : P₁ = P x q :=
      Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hR.card_P, hcard, hk6])
    exact hxP₁ (hPeq ▸ le_sup_right (a := Q q) (mem_zpowers x))
  have hQeq : Q q = P₁ := Subgroup.eq_of_le_of_card_ge hQP₁ (by rw [hR.card_Q, hcard, hk'])
  rw [hQeq]
  exact ⟨hu, ⟨⟨u, hR.P_le_K hu⟩, MonoidHom.mem_ker.2 (Units.ext (by
    rw [hR.AU_val, Units.val_one]; exact hA)), rfl⟩⟩

end Rel

end CFSG.RankThree.Native.FiveLocal
