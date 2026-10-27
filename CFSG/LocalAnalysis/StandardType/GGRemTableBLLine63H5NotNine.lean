module

public import CFSG.LocalAnalysis.StandardType.GGRemTableBLLine63H5Det
public import CFSG.LocalAnalysis.StandardType.GGRemTableBLLine63H5Nine

public section

namespace CFSG.StandardType.Line63.H5

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.SectionRank.OddCover

variable {K : Type} [Field K] {n : ℕ}

theorem coprime_three_two_pow_sub_one (hn : 1 ≤ n) (hpq : 3 ∣ 2 ^ n + 1) :
    Nat.Coprime 3 (2 ^ n - 1) := by
  rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_three]
  intro h
  have h2 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  have h3 : 3 ∣ (2 ^ n + 1) - (2 ^ n - 1) := Nat.dvd_sub hpq h
  have : (2 ^ n + 1) - (2 ^ n - 1) = 2 := by omega
  rw [this] at h3
  omega

theorem not_cube_of_not_nine_dvd [Finite K] (hKd : UnitaryFieldData 2 n K) (hpq : 3 ∣ 2 ^ n + 1)
    (h9 : ¬ 9 ∣ 2 ^ n + 1) {z : Kˣ} (hz3 : z ^ 3 = 1) (hz1 : z ≠ 1) :
    ∀ d : K, d ^ 3 ≠ (z : K) := by
  intro d hd
  have hd0 : d ≠ 0 := by
    rintro rfl
    exact z.ne_zero (by rw [← hd]; norm_num)
  set d' : Kˣ := Units.mk0 d hd0 with hd'
  have hd3 : d' ^ 3 = z := Units.ext (by rw [Units.val_pow_eq_pow_val, hd', Units.val_mk0, hd])
  have hd9 : d' ^ 9 = 1 := by
    rw [show d' ^ 9 = (d' ^ 3) ^ 3 by group, hd3, hz3]
  have hord : orderOf d' = 9 := by
    have h1 : orderOf d' ∣ 9 := orderOf_dvd_of_pow_eq_one hd9
    have h2 : orderOf d' ∣ 3 ∨ orderOf d' = 9 := by
      have : orderOf d' ∣ 3 ^ 2 := by simpa using h1
      obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp this
      interval_cases k
      · left; simp [hk']
      · left; simp [hk']
      · right; simp [hk']
    rcases h2 with h2 | h2
    · exfalso
      apply hz1
      rw [← hd3]
      exact orderOf_dvd_iff_pow_eq_one.mp h2
    · exact h2
  have hdiv : 9 ∣ Nat.card Kˣ := hord ▸ orderOf_dvd_natCard d'
  have hn : 1 ≤ n := hKd.one_le
  rw [Nat.card_units, hKd.card, pow_mul', sq] at hdiv
  have e := Nat.mul_self_sub_mul_self_eq (2 ^ n) 1
  rw [mul_one] at e
  rw [e] at hdiv
  have hcop : Nat.Coprime 9 (2 ^ n - 1) := by
    have := (coprime_three_two_pow_sub_one hn hpq).pow_left 2
    simpa using this
  exact h9 ((hcop.dvd_of_dvd_mul_left (by rwa [mul_comm] at hdiv)))

theorem false_of_pow_three_eq_scalar [Finite K] (hKd : UnitaryFieldData 2 n K)
    (hpq : 3 ∣ 2 ^ n + 1) (h9 : ¬ 9 ∣ 2 ^ n + 1) {z : Kˣ} (hz3 : z ^ 3 = 1) (hz1 : z ≠ 1)
    (ℓ : ↥(unitarySU 2 n K 6)) (hℓ : ℓ ^ 3 = scalarSU hKd hpq hz3) : False := by
  have hM : ((ℓ : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) ^ 3 =
      (z : K) • (1 : Matrix (Fin 6) (Fin 6) K) := by
    have h1 : (ℓ : GL (Fin 6) K) ^ 3 = diagHom 6 (fun _ => z) := congrArg Subtype.val hℓ
    have h2 := congrArg (fun g : GL (Fin 6) K => (g : Matrix (Fin 6) (Fin 6) K)) h1
    simp only [Units.val_pow_eq_pow_val, coe_diagHom] at h2
    rw [h2]
    ext i j
    simp [Matrix.diagonal_apply, Matrix.one_apply]
  have hdet := det_eq_sq_of_pow_three_eq_smul (not_cube_of_not_nine_dvd hKd hpq h9 hz3 hz1) hM
  have h1 := ((mem_unitarySU_iff hKd).mp ℓ.2).1
  rw [hdet] at h1
  apply hz1
  apply Units.ext
  rw [Units.val_one]
  have hz3' : (z : K) ^ 3 = 1 := by
    rw [← Units.val_pow_eq_pow_val, hz3]
    simp
  calc (z : K) = (z : K) ^ 3 / (z : K) ^ 2 := by
        field_simp
    _ = 1 := by rw [hz3', h1]; simp

end CFSG.StandardType.Line63.H5

end
