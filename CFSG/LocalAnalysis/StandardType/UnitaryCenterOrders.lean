module

public import CFSG.LocalAnalysis.StandardType.UnitaryCenterScalar

public section

namespace CFSG.StandardType

namespace UnitaryCenter

open Matrix CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits

theorem not_seven_dvd_two_pow_add_one (f : ℕ) : ¬ 7 ∣ 2 ^ f + 1 := by
  have key : 2 ^ f % 7 = 1 ∨ 2 ^ f % 7 = 2 ∨ 2 ^ f % 7 = 4 := by
    induction f with
    | zero => norm_num
    | succ f ih =>
      rw [pow_succ, Nat.mul_mod]
      rcases ih with h | h | h <;> rw [h] <;> norm_num
  intro h7
  have hmod : (2 ^ f + 1) % 7 = 0 := Nat.mod_eq_zero_of_dvd h7
  rw [Nat.add_mod] at hmod
  rcases key with h | h | h <;> rw [h] at hmod <;> norm_num at hmod

theorem three_dvd_two_pow_add_one_of_odd {f : ℕ} (hf : Odd f) : 3 ∣ 2 ^ f + 1 := by
  rcases hf with ⟨k, rfl⟩
  have h4 : 4 ^ k % 3 = 1 := by
    induction k with
    | zero => norm_num
    | succ k ih => rw [pow_succ, Nat.mul_mod, ih]
  apply Nat.dvd_iff_mod_eq_zero.mpr
  have hpow : 2 ^ (2 * k + 1) = 2 * 4 ^ k := by
    rw [pow_succ', pow_mul]
    norm_num
  rw [hpow, Nat.add_mod, Nat.mul_mod, h4]

theorem not_three_dvd_two_pow_add_one_of_even {f : ℕ} (hf : Even f) : ¬ 3 ∣ 2 ^ f + 1 := by
  rcases hf with ⟨k, rfl⟩
  have h4 : 4 ^ k % 3 = 1 := by
    induction k with
    | zero => norm_num
    | succ k ih => rw [pow_succ, Nat.mul_mod, ih]
  intro h
  have hmod : (2 ^ (k + k) + 1) % 3 = 0 := Nat.mod_eq_zero_of_dvd h
  have hpow : 2 ^ (k + k) = 4 ^ k := by
    rw [pow_add, ← mul_pow]
    norm_num
  rw [hpow, Nat.add_mod, h4] at hmod
  norm_num at hmod

theorem odd_two_pow_add_one {f : ℕ} (hf : 1 ≤ f) : Odd (2 ^ f + 1) := by
  exact Even.add_one (Nat.even_pow.mpr ⟨even_two, by omega⟩)

variable {F : Type} [Field F] [Finite F] [CharP F 2] {f n : ℕ}

theorem scalar_injective {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] {R : Type*}
    [Semiring R] : Function.Injective (Matrix.GeneralLinearGroup.scalar ι : Rˣ →* GL ι R) := by
  intro a b h
  have h' : Matrix.scalar ι (a : R) = Matrix.scalar ι (b : R) := by
    simpa only [Matrix.GeneralLinearGroup.coe_scalar] using
      congrArg (fun g : Matrix.GeneralLinearGroup ι R => (g : Matrix ι ι R)) h
  exact Units.ext (Matrix.scalar_inj.mp h')

theorem pow_eq_one_of_scalar {k : ℕ} {c : Fˣ} {z : SU (unitaryInvolution F 2 f) n}
    (hc : (z : GL (Fin n) F) = Matrix.GeneralLinearGroup.scalar (Fin n) c) (hn : 0 < n)
    (hk : z ^ k = 1) : c ^ k = 1 := by
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hk' : (z : GL (Fin n) F) ^ k = 1 := by
    have := congrArg (fun w : SU (unitaryInvolution F 2 f) n => (w : GL (Fin n) F)) hk
    simpa using this
  have hsc : Matrix.GeneralLinearGroup.scalar (Fin n) (c ^ k) =
      Matrix.GeneralLinearGroup.scalar (Fin n) 1 := by
    rw [map_pow, ← hc, hk', map_one]
  exact scalar_injective hsc

theorem eq_one_of_scalar_pow_of_coprime {k m : ℕ} {c : Fˣ}
    {z : SU (unitaryInvolution F 2 f) n}
    (hc : (z : GL (Fin n) F) = Matrix.GeneralLinearGroup.scalar (Fin n) c) (hn : 0 < n)
    (hkm : Nat.Coprime k m) (hcm : c ^ m = 1) (hk : z ^ k = 1) : z = 1 := by
  have hck : c ^ k = 1 := pow_eq_one_of_scalar hc hn hk
  have hcg : c ^ Nat.gcd k m = 1 := pow_gcd_eq_one.mpr ⟨hck, hcm⟩
  rw [hkm.gcd_eq_one, pow_one] at hcg
  apply Subtype.ext
  rw [Subgroup.coe_one, hc, hcg, map_one]

theorem eq_one_of_mem_center_of_pow_seven (hF : Nat.card F = (2 ^ f) ^ 2) (hf : 1 ≤ f) (hn : 3 ≤ n)
    {z : SU (unitaryInvolution F 2 f) n} (hz : z ∈ Subgroup.center (SU (unitaryInvolution F 2 f) n))
    (h7 : z ^ 7 = 1) : z = 1 := by
  obtain ⟨c, hc, -, hcm⟩ := exists_scalar_of_mem_center hF hf hn hz
  have hcop : Nat.Coprime 7 (2 ^ f + 1) :=
    (by norm_num : Nat.Prime 7).coprime_iff_not_dvd.mpr (not_seven_dvd_two_pow_add_one f)
  exact eq_one_of_scalar_pow_of_coprime hc (by omega) hcop hcm h7

theorem eq_one_of_mem_center_of_pow_five (hF : Nat.card F = (2 ^ f) ^ 2) (hf : 1 ≤ f) (hn6 : 6 ≤ n)
    (hn9 : n ≤ 9) {z : SU (unitaryInvolution F 2 f) n}
    (hz : z ∈ Subgroup.center (SU (unitaryInvolution F 2 f) n)) (h5 : z ^ 5 = 1) : z = 1 := by
  obtain ⟨c, hc, hcn, -⟩ := exists_scalar_of_mem_center hF hf (by omega) hz
  have hcop : Nat.Coprime 5 n := by
    interval_cases n <;> norm_num
  exact eq_one_of_scalar_pow_of_coprime hc (by omega) hcop hcn h5

theorem eq_one_of_mem_center_of_pow_three (hF : Nat.card F = (2 ^ f) ^ 2) (hf : 1 ≤ f) (hn : 3 ≤ n)
    (hfe : Even f) {z : SU (unitaryInvolution F 2 f) n}
    (hz : z ∈ Subgroup.center (SU (unitaryInvolution F 2 f) n)) (h3 : z ^ 3 = 1) : z = 1 := by
  obtain ⟨c, hc, -, hcm⟩ := exists_scalar_of_mem_center hF hf hn hz
  have hcop : Nat.Coprime 3 (2 ^ f + 1) :=
    (by norm_num : Nat.Prime 3).coprime_iff_not_dvd.mpr
      (not_three_dvd_two_pow_add_one_of_even hfe)
  exact eq_one_of_scalar_pow_of_coprime hc (by omega) hcop hcm h3

theorem eq_one_of_mem_center_of_mem_isPGroup_two (hF : Nat.card F = (2 ^ f) ^ 2) (hf : 1 ≤ f)
    (hn : 3 ≤ n) {U : Subgroup (SU (unitaryInvolution F 2 f) n)} (hU : IsPGroup 2 U)
    {z : SU (unitaryInvolution F 2 f) n}
    (hz : z ∈ Subgroup.center (SU (unitaryInvolution F 2 f) n)) (hzU : z ∈ U) : z = 1 := by
  obtain ⟨k, hk⟩ := isPGroup_iff_pow_pow_eq_one.mp hU ⟨z, hzU⟩
  have hzk : z ^ (2 ^ k) = 1 := by
    have := congrArg (fun w : U => (w : SU (unitaryInvolution F 2 f) n)) hk
    simpa using this
  obtain ⟨c, hc, -, hcm⟩ := exists_scalar_of_mem_center hF hf hn hz
  have hcop : Nat.Coprime (2 ^ k) (2 ^ f + 1) :=
    Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr (odd_two_pow_add_one hf))
  exact eq_one_of_scalar_pow_of_coprime hc (by omega) hcop hcm hzk

end UnitaryCenter

end CFSG.StandardType
