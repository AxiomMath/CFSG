module

public import CFSG.LieType.BorelTits.UnitaryForm
public import CFSG.LocalAnalysis.StandardType.UnitaryCenterOrders
public import Mathlib.GroupTheory.Perm.Cycle.Type

public section

namespace CFSG.StandardType

namespace UnitaryCubeRoots

open CFSG.LieType.BorelTits

variable {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}

lemma not_three_dvd_two_pow (f : ℕ) : ¬ 3 ∣ 2 ^ f := by
  intro h
  have h2 : 3 ∣ 2 := Nat.prime_three.dvd_of_dvd_pow h
  norm_num at h2

lemma two_pow_mod_three_ne_zero (f : ℕ) : 2 ^ f % 3 ≠ 0 :=
  fun h => not_three_dvd_two_pow f (Nat.dvd_iff_mod_eq_zero.mpr h)

lemma three_dvd_sq_sub_one_of_mod_ne_zero {q : ℕ} (hq : q % 3 ≠ 0) : 3 ∣ q ^ 2 - 1 := by
  have hsq : q ^ 2 % 3 = 1 := by
    have hlt : q % 3 < 3 := Nat.mod_lt _ (by norm_num)
    have hcases : q % 3 = 1 ∨ q % 3 = 2 := by omega
    rw [pow_two, Nat.mul_mod]
    rcases hcases with h | h <;> rw [h] <;> norm_num
  obtain ⟨m, hm⟩ : ∃ m, q ^ 2 = 3 * m + 1 := by
    refine ⟨q ^ 2 / 3, ?_⟩
    have h := Nat.div_add_mod (q ^ 2) 3
    omega
  exact ⟨m, by omega⟩

lemma two_pow_mod_three_of_odd {f : ℕ} (hf : Odd f) : 2 ^ f % 3 = 2 := by
  have h0 : (2 ^ f + 1) % 3 = 0 :=
    Nat.mod_eq_zero_of_dvd (UnitaryCenter.three_dvd_two_pow_add_one_of_odd hf)
  have hlt : 2 ^ f % 3 < 3 := Nat.mod_lt _ (by norm_num)
  have hne : 2 ^ f % 3 ≠ 0 := two_pow_mod_three_ne_zero f
  omega

lemma two_pow_mod_three_of_even {f : ℕ} (hf : Even f) : 2 ^ f % 3 = 1 := by
  have hndvd := UnitaryCenter.not_three_dvd_two_pow_add_one_of_even hf
  have h0 : (2 ^ f + 1) % 3 ≠ 0 := fun h => hndvd (Nat.dvd_of_mod_eq_zero h)
  have hlt : 2 ^ f % 3 < 3 := Nat.mod_lt _ (by norm_num)
  have hne0 : 2 ^ f % 3 ≠ 0 := two_pow_mod_three_ne_zero f
  omega

theorem exists_cubeRoot (hF : Nat.card F = (2 ^ f) ^ 2) (hf : 1 ≤ f) :
    ∃ ζ : F, ζ ≠ 1 ∧ ζ ^ 3 = 1 := by
  have hdvd : 3 ∣ Nat.card Fˣ := by
    rw [Nat.card_units, hF]
    exact three_dvd_sq_sub_one_of_mod_ne_zero (two_pow_mod_three_ne_zero f)
  obtain ⟨ω, hω⟩ := exists_prime_orderOf_dvd_card' (G := Fˣ) 3 hdvd
  refine ⟨(ω : F), ?_, ?_⟩
  · intro h
    have hu : ω = 1 := Units.ext h
    rw [hu, orderOf_one] at hω
    omega
  · have h1 : ω ^ 3 = 1 := by rw [← hω]; exact pow_orderOf_eq_one ω
    have h2 : ((ω : F)) ^ 3 = 1 := by
      have := congrArg (fun x : Fˣ => (x : F)) h1
      simpa using this
    exact h2

theorem exists_cubeRoot_inv_of_odd (hF : Nat.card F = (2 ^ f) ^ 2) (hf : 1 ≤ f) (hfo : Odd f) :
    ∃ ζ : F, ζ ≠ 1 ∧ ζ ^ 3 = 1 ∧ unitaryInvolution F 2 f ζ = ζ⁻¹ := by
  obtain ⟨ζ, hζ1, hζ3⟩ := exists_cubeRoot hF hf
  refine ⟨ζ, hζ1, hζ3, ?_⟩
  have hpow : ζ ^ (2 ^ f) = ζ ^ 2 := by
    obtain ⟨t, ht⟩ : ∃ t, 2 ^ f = 3 * t + 2 := by
      refine ⟨2 ^ f / 3, ?_⟩
      have h := Nat.div_add_mod (2 ^ f) 3
      have hm := two_pow_mod_three_of_odd hfo
      omega
    rw [ht, pow_add, pow_mul, hζ3, one_pow, one_mul]
  have hsq : ζ ^ 2 = ζ⁻¹ := by
    have h : ζ ^ 2 * ζ = 1 := by rw [← pow_succ]; exact hζ3
    exact eq_inv_of_mul_eq_one_left h
  rw [unitaryInvolution_apply, hpow, hsq]

theorem exists_cubeRoot_fixed_of_even (hF : Nat.card F = (2 ^ f) ^ 2) (hf : 1 ≤ f) (hfe : Even f) :
    ∃ ζ : F, ζ ≠ 1 ∧ ζ ^ 3 = 1 ∧ unitaryInvolution F 2 f ζ = ζ := by
  obtain ⟨ζ, hζ1, hζ3⟩ := exists_cubeRoot hF hf
  refine ⟨ζ, hζ1, hζ3, ?_⟩
  have hpow : ζ ^ (2 ^ f) = ζ := by
    obtain ⟨t, ht⟩ : ∃ t, 2 ^ f = 3 * t + 1 := by
      refine ⟨2 ^ f / 3, ?_⟩
      have h := Nat.div_add_mod (2 ^ f) 3
      have hm := two_pow_mod_three_of_even hfe
      omega
    rw [ht, pow_add, pow_mul, hζ3, one_pow, one_mul, pow_one]
  rw [unitaryInvolution_apply, hpow]

end UnitaryCubeRoots

end CFSG.StandardType
