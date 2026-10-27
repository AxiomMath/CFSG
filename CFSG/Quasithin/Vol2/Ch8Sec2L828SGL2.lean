module

public import Mathlib.GroupTheory.SpecificGroups.Dihedral
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
public import Mathlib.FieldTheory.Finite.Basic

public section

namespace CFSG.Quasithin.H13.L828SGL2

private lemma l828_two_eq_zero (K : Type) [Field K] [Finite K] (hK : Nat.card K = 4) :
    (2 : K) = 0 := by
  haveI : Fintype K := Fintype.ofFinite K
  have hc : Fintype.card K = 4 := by rw [← Nat.card_eq_fintype_card]; exact hK
  have h4 : ((Fintype.card K : ℕ) : K) = 0 := FiniteField.cast_card_eq_zero K
  rw [hc] at h4
  have h4' : (4 : K) = 0 := by exact_mod_cast h4
  have h22 : (2 : K) * 2 = 0 := by linear_combination h4'
  rcases mul_eq_zero.mp h22 with h | h <;> exact h

private lemma l828_pow_four (K : Type) [Field K] [Finite K] (hK : Nat.card K = 4) (t : K) :
    t ^ 4 = t := by
  haveI : Fintype K := Fintype.ofFinite K
  have hc : Fintype.card K = 4 := by rw [← Nat.card_eq_fintype_card]; exact hK
  have h := FiniteField.pow_card t
  rw [hc] at h
  exact h

private lemma l828_cayley_hamilton {K : Type} [CommRing K] (g : Matrix (Fin 2) (Fin 2) K) :
    g * g = g.trace • g - g.det • (1 : Matrix (Fin 2) (Fin 2) K) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.trace_fin_two, Matrix.det_fin_two,
      Matrix.one_apply] <;> ring

private lemma l828_pow_cases {K : Type} [Field K] (h2 : (2 : K) = 0)
    (g : Matrix (Fin 2) (Fin 2) K) (t : K) (ht4 : t ^ 4 = t) (hCH : g * g = t • g - 1) :
    g ^ 2 = 1 ∨ g ^ 3 = 1 ∨ g ^ 5 = 1 := by
  have hm1 : (-1 : K) = 1 := by linear_combination -h2
  have hmulg : ∀ α β : K, g * (α • g + β • (1 : Matrix (Fin 2) (Fin 2) K))
      = (α * t + β) • g + (-α) • (1 : Matrix (Fin 2) (Fin 2) K) := by
    intro α β
    rw [mul_add, mul_smul_comm, mul_smul_comm, mul_one, hCH]
    module
  have hp2 : g ^ 2 = t • g + (-1 : K) • (1 : Matrix (Fin 2) (Fin 2) K) := by
    rw [sq, hCH]
    module
  have hp3 : g ^ 3 = (t * t + -1) • g + (-t) • (1 : Matrix (Fin 2) (Fin 2) K) := by
    rw [show g ^ 3 = g * g ^ 2 from pow_succ' g 2, hp2, hmulg]
  have hp4 : g ^ 4 = ((t * t + -1) * t + -t) • g
      + (-(t * t + -1)) • (1 : Matrix (Fin 2) (Fin 2) K) := by
    rw [show g ^ 4 = g * g ^ 3 from pow_succ' g 3, hp3, hmulg]
  have hp5 : g ^ 5 = (((t * t + -1) * t + -t) * t + -(t * t + -1)) • g
      + (-((t * t + -1) * t + -t)) • (1 : Matrix (Fin 2) (Fin 2) K) := by
    rw [show g ^ 5 = g * g ^ 4 from pow_succ' g 4, hp4, hmulg]
  have hfac : t * ((t + 1) * (t ^ 2 + t + 1)) = 0 := by
    linear_combination ht4 + (t ^ 3 + t ^ 2 + t) * h2
  rcases mul_eq_zero.mp hfac with ht0 | hrest
  · left
    rw [hp2, ht0, zero_smul, zero_add, hm1, one_smul]
  · rcases mul_eq_zero.mp hrest with h1 | h3
    · right
      left
      have ht1 : t = 1 := by linear_combination h1 - h2
      have e1 : t * t + -1 = (0 : K) := by linear_combination (t + 1) * ht1
      have e2 : -t = (1 : K) := by linear_combination -ht1 - h2
      rw [hp3, e1, e2, zero_smul, zero_add, one_smul]
    · right
      right
      have e1 : ((t * t + -1) * t + -t) * t + -(t * t + -1) = (0 : K) := by
        linear_combination (t ^ 2 - t - 3) * h3 + (2 * t + 2) * h2
      have e2 : -((t * t + -1) * t + -t) = (1 : K) := by
        linear_combination (1 - t) * h3 + (t - 1) * h2
      rw [hp5, e1, e2, zero_smul, zero_add, one_smul]

theorem stmt_a (K : Type) [Field K] [Finite K] (hK : Nat.card K = 4)
    (g : Matrix (Fin 2) (Fin 2) K) (hg : g.det = 1) : g ^ 2 = 1 ∨ g ^ 3 = 1 ∨ g ^ 5 = 1 := by
  have hCH : g * g = g.trace • g - 1 := by
    have h := l828_cayley_hamilton g
    rw [hg, one_smul] at h
    exact h
  exact l828_pow_cases (l828_two_eq_zero K hK) g g.trace (l828_pow_four K hK g.trace) hCH

private lemma l828_pow_eq_one_of_val {K : Type} [Field K]
    (x : Matrix.GeneralLinearGroup (Fin 2) K) (k : ℕ)
    (h : (x : Matrix (Fin 2) (Fin 2) K) ^ k = 1) : x ^ k = 1 := by
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, Units.val_one]
  exact h

private lemma l828_scalar_det {K : Type} [Field K] (h2 : (2 : K) = 0) (a b e : K)
    (e1 : 1 = e * e) (e2 : 1 = b * a) (e3 : b = e * a * e) : a = 1 := by
  have hab : b = a := by linear_combination e3 - a * e1
  have haa : a * a = 1 := by linear_combination -e2 - a * hab
  have hsq : (a - 1) ^ 2 = 0 := by linear_combination haa + (1 - a) * h2
  have h0 : a - 1 = 0 := (pow_eq_zero_iff two_ne_zero).mp hsq
  exact sub_eq_zero.mp h0

private lemma l828_det_eq_one {K : Type} [Field K] (h2 : (2 : K) = 0)
    (s x : Matrix.GeneralLinearGroup (Fin 2) K) (hss : s * s = 1) (hrel : s * x * s = x⁻¹) :
    (x : Matrix (Fin 2) (Fin 2) K).det = 1 := by
  have hmul : ∀ g h : Matrix.GeneralLinearGroup (Fin 2) K,
      ((g * h : Matrix.GeneralLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).det
        = (g : Matrix (Fin 2) (Fin 2) K).det * (h : Matrix (Fin 2) (Fin 2) K).det := by
    intro g h
    rw [Units.val_mul, Matrix.det_mul]
  have e1 := hmul s s
  rw [hss, Units.val_one, Matrix.det_one] at e1
  have e2 := hmul x⁻¹ x
  rw [inv_mul_cancel, Units.val_one, Matrix.det_one] at e2
  have e3 := hmul (s * x) s
  rw [hrel, hmul] at e3
  exact l828_scalar_det h2 _ _ _ e1 e2 e3

theorem stmt_b (K : Type) [Field K] [Finite K] (hK : Nat.card K = 4) (m : ℕ) (hm : Odd m)
    (hm1 : 1 < m) (f : DihedralGroup m →* Matrix.GeneralLinearGroup (Fin 2) K)
    (hf : Function.Injective f) : m = 3 ∨ m = 5 := by
  have h2 : (2 : K) = 0 := l828_two_eq_zero K hK
  have hord : orderOf (f (DihedralGroup.r 1)) = m := by
    rw [orderOf_injective f hf, DihedralGroup.orderOf_r_one]
  have h1 : (DihedralGroup.sr 0 : DihedralGroup m) * DihedralGroup.r 1 * DihedralGroup.sr 0
      = (DihedralGroup.r 1)⁻¹ := by
    rw [DihedralGroup.sr_mul_r, DihedralGroup.sr_mul_sr, DihedralGroup.inv_r]
    congr 1
    ring
  have hrel : f (DihedralGroup.sr 0) * f (DihedralGroup.r 1) * f (DihedralGroup.sr 0)
      = (f (DihedralGroup.r 1))⁻¹ := by
    rw [← map_mul, ← map_mul, h1, map_inv]
  have hss : f (DihedralGroup.sr 0) * f (DihedralGroup.sr 0) = 1 := by
    rw [← map_mul, DihedralGroup.sr_mul_self, map_one]
  have hdet := l828_det_eq_one h2 _ _ hss hrel
  have hpow := stmt_a K hK _ hdet
  have hdvd : ∀ k : ℕ, (f (DihedralGroup.r 1) : Matrix (Fin 2) (Fin 2) K) ^ k = 1 → m ∣ k := by
    intro k hk
    have hk' : f (DihedralGroup.r 1) ^ k = 1 := l828_pow_eq_one_of_val _ k hk
    have hd := orderOf_dvd_of_pow_eq_one hk'
    rwa [hord] at hd
  have hdiv : m ∣ 2 ∨ m ∣ 3 ∨ m ∣ 5 := by
    rcases hpow with h | h | h
    · exact Or.inl (hdvd 2 h)
    · exact Or.inr (Or.inl (hdvd 3 h))
    · exact Or.inr (Or.inr (hdvd 5 h))
  obtain ⟨k, hk⟩ := hm
  rcases hdiv with h | h | h
  · rcases (Nat.dvd_prime Nat.prime_two).mp h with h' | h' <;> omega
  · rcases (Nat.dvd_prime Nat.prime_three).mp h with h' | h' <;> omega
  · rcases (Nat.dvd_prime Nat.prime_five).mp h with h' | h' <;> omega

theorem stmt_c (K : Type) [Field K] [Finite K] (hK : Nat.card K = 2) (m : ℕ) (hm : Odd m)
    (hm1 : 1 < m) (f : DihedralGroup m →* Matrix.GeneralLinearGroup (Fin 2) K)
    (hf : Function.Injective f) : m = 3 := by
  haveI : Fintype K := Fintype.ofFinite K
  have hc : Fintype.card K = 2 := by rw [← Nat.card_eq_fintype_card]; exact hK
  haveI : Finite (Matrix.GeneralLinearGroup (Fin 2) K) :=
    Finite.of_injective (fun g : Matrix.GeneralLinearGroup (Fin 2) K =>
      (g : Matrix (Fin 2) (Fin 2) K)) (fun a b h => Units.ext h)
  have hle := Nat.card_le_card_of_injective f hf
  rw [DihedralGroup.nat_card, Matrix.card_GL_field, hc] at hle
  norm_num [Fin.prod_univ_two] at hle
  obtain ⟨k, hk⟩ := hm
  omega

end CFSG.Quasithin.H13.L828SGL2
