module

public import CFSG.RankThree.PartTwo.Sec4.LThreePiDefs
import CFSG.ClassicalGroups.Unitary.Finite

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148W

open CFSG.RankThree.PartTwo.Sec4 Matrix CFSG.LocalAnalysis.ComponentInitial

variable {K : Type} [Field K] {p f : ℕ}

@[expose] def diagOne (t : Kˣ) : GL (Fin 2) K :=
  ⟨diagonal ![1, (t : K)], diagonal ![1, ((t⁻¹ : Kˣ) : K)],
    by
      rw [diagonal_mul_diagonal, ← diagonal_one]
      congr 1
      funext i
      fin_cases i <;> simp,
    by
      rw [diagonal_mul_diagonal, ← diagonal_one]
      congr 1
      funext i
      fin_cases i <;> simp⟩

theorem coe_diagOne (t : Kˣ) :
    ((diagOne t : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = diagonal ![1, (t : K)] :=
  rfl

theorem diagOne_mem_glPi (h : UnitaryFieldData p f K) (hq : p ^ f % 3 = 2) {τ : Kˣ}
    (hτ : τ ^ 3 = 1) : diagOne τ ∈ glPi false 2 (p ^ f) K := by
  have hτ3 : (τ : K) ^ 3 = 1 := by
    have := congrArg Units.val hτ
    rwa [Units.val_pow_eq_pow_val, Units.val_one] at this
  have hbar : h.bar (τ : K) * (τ : K) = 1 := by
    rw [h.bar_apply, ← pow_succ]
    exact pow_succ_eq_one_of_modThree hq hτ3
  rw [mem_glPi_false h, coe_diagOne, diagonal_map (map_zero _), diagonal_transpose,
    diagonal_mul_diagonal, ← diagonal_one]
  congr 1
  funext i
  fin_cases i
  · simp
  · simpa using hbar

private theorem fin2_ext {x y z w x' y' z' w' : K} (h1 : x = x') (h2 : y = y') (h3 : z = z')
    (h4 : w = w') : (!![x, y; z, w] : Matrix (Fin 2) (Fin 2) K) = !![x', y'; z', w'] := by
  subst h1 h2 h3 h4
  rfl

private theorem diagOne_fin2 (τ : Kˣ) :
    ((diagOne τ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = !![1, 0; 0, (τ : K)] := by
  rw [coe_diagOne]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

private theorem diagOne_inv_fin2 (τ : Kˣ) :
    (((diagOne τ)⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      !![1, 0; 0, ((τ⁻¹ : Kˣ) : K)] := by
  show diagonal ![1, ((τ⁻¹ : Kˣ) : K)] = _
  ext i j
  fin_cases i <;> fin_cases j <;> simp

private theorem neg_one_fin2 : (-1 : Matrix (Fin 2) (Fin 2) K) = !![-1, 0; 0, -1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp

private theorem exists_glFin2 (a b B : K) (hdet : B * b - a ^ 2 = 1) :
    ∃ i : GL (Fin 2) K, (i : Matrix (Fin 2) (Fin 2) K) = !![a, b; -B, -a] := by
  refine ⟨⟨!![a, b; -B, -a], !![-a, -b; B, a], ?_, ?_⟩, rfl⟩
  · rw [Matrix.mul_fin_two, Matrix.one_fin_two]
    apply fin2_ext
    · linear_combination hdet
    · ring
    · ring
    · linear_combination hdet
  · rw [Matrix.mul_fin_two, Matrix.one_fin_two]
    apply fin2_ext
    · linear_combination hdet
    · ring
    · ring
    · linear_combination hdet

theorem exists_quaternion_frame (h : UnitaryFieldData p f K) (hq : p ^ f % 3 = 2) (hp2 : p ≠ 2)
    {τ : Kˣ} (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1) :
    ∃ i₀ : GL (Fin 2) K, i₀ ∈ glPi false 2 (p ^ f) K ∧ i₀ * i₀ = -1 ∧
      i₀ * (diagOne τ * i₀ * (diagOne τ)⁻¹) =
        diagOne τ * (diagOne τ * i₀ * (diagOne τ)⁻¹) * (diagOne τ)⁻¹ ∧
      diagOne τ * i₀ * (diagOne τ)⁻¹ ≠ i₀ := by
  have hfin := h.finite
  haveI : Fact p.Prime := ⟨h.prime⟩
  have hchar := h.charP
  have hK : Nat.card K = (p ^ f) ^ 2 := by rw [h.card, ← pow_mul, mul_comm]
  have hτ3 : (τ : K) ^ 3 = 1 := by
    have := congrArg Units.val hτ
    rwa [Units.val_pow_eq_pow_val, Units.val_one] at this
  have hsinv : ((τ⁻¹ : Kˣ) : K) = (τ : K) ^ 2 := by
    rw [Units.val_inv_eq_inv_val]
    exact inv_eq_of_mul_eq_one_right (by linear_combination hτ3)
  have ht1 : (τ : K) - 1 ≠ 0 :=
    sub_ne_zero.mpr fun e => hτ1 (Units.ext (by rw [Units.val_one]; exact e))
  have ht2 : (τ : K) ^ 2 + (τ : K) + 1 = 0 :=
    (mul_eq_zero.mp (show ((τ : K) - 1) * ((τ : K) ^ 2 + (τ : K) + 1) = 0 by
      linear_combination hτ3)).resolve_left ht1
  have h3 : (3 : K) ≠ 0 := by
    intro h0
    have hdvd : p ∣ 3 := (CharP.cast_eq_zero_iff K p 3).mp (by exact_mod_cast h0)
    have hp : p = 3 := (Nat.prime_dvd_prime_iff_eq h.prime Nat.prime_three).mp hdvd
    subst hp
    have : 3 ∣ 3 ^ f := dvd_pow_self 3 (by have := h.one_le; omega)
    omega
  have h2 : (2 : K) ≠ 0 := by
    intro h0
    have hdvd : p ∣ 2 := (CharP.cast_eq_zero_iff K p 2).mp (by exact_mod_cast h0)
    exact hp2 ((Nat.prime_dvd_prime_iff_eq h.prime Nat.prime_two).mp hdvd)
  have h23 : (2 / 3 : K) ≠ 0 := div_ne_zero h2 h3
  have htq : (τ : K) ^ p ^ f = (τ : K) ^ 2 := by
    obtain ⟨k, hk⟩ : ∃ k, p ^ f = 3 * k + 2 := ⟨p ^ f / 3, by omega⟩
    rw [hk, pow_add, pow_mul, hτ3, one_pow, one_mul]
  have hbar_t : h.bar (τ : K) = (τ : K) ^ 2 := by rw [h.bar_apply, htq]
  have hσ : ∀ x : K, CFSG.LieType.BorelTits.unitaryInvolution K p f x = h.bar x := fun x => by
    rw [CFSG.LieType.BorelTits.unitaryInvolution_apply, h.bar_apply]
  obtain ⟨b, hb⟩ : ∃ c : K, h.bar c * c = 2 / 3 := by
    have hfix : CFSG.LieType.BorelTits.unitaryInvolution K p f (2 / 3) = 2 / 3 := by
      rw [hσ, map_div₀, map_ofNat, map_ofNat]
    obtain ⟨c, hc⟩ := CFSG.ClassicalGroups.Unitary.exists_norm_eq_of_fixed hK hfix h23
    exact ⟨c, by rwa [hσ] at hc⟩
  have hb0 : b ≠ 0 := by
    rintro rfl
    rw [map_zero, zero_mul] at hb
    exact h23 hb.symm
  have hP3 : 3 * (h.bar b * b) = 2 := by rw [hb]; field_simp
  obtain ⟨a, ha3⟩ : ∃ a : K, 3 * a = -(1 + 2 * (τ : K)) :=
    ⟨-(1 + 2 * (τ : K)) / 3, by field_simp⟩
  have ha2 : 3 * a ^ 2 = -1 := by
    have h0 : (3 : K) * (3 * a ^ 2 + 1) = 0 := by
      linear_combination (3 * a - 1 - 2 * (τ : K)) * ha3 + 4 * ht2
    linear_combination (mul_eq_zero.mp h0).resolve_left h3
  have hdet : h.bar b * b - a ^ 2 = 1 := by
    have h0 : (3 : K) * (h.bar b * b - a ^ 2 - 1) = 0 := by
      linear_combination hP3 - ha2
    linear_combination (mul_eq_zero.mp h0).resolve_left h3
  have hbar_a : h.bar a = -a := by
    have hha : h.bar (3 * a) = h.bar (-(1 + 2 * (τ : K))) := congrArg h.bar ha3
    simp only [map_mul, map_neg, map_add, map_one, map_ofNat, hbar_t] at hha
    have h0 : (3 : K) * (h.bar a + a) = 0 := by
      linear_combination hha + ha3 - 2 * ht2
    linear_combination (mul_eq_zero.mp h0).resolve_left h3
  have hT : ((!![a, b; -h.bar b, -a] : Matrix (Fin 2) (Fin 2) K).map h.bar)ᵀ =
      !![-a, -b; h.bar b, a] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hbar_a, h.bar_bar]
  obtain ⟨i₀, hi⟩ := exists_glFin2 a b (h.bar b) hdet
  refine ⟨i₀, ?_, ?_, ?_, ?_⟩
  · rw [mem_glPi_false h, hi, hT, Matrix.mul_fin_two, Matrix.one_fin_two]
    apply fin2_ext
    · linear_combination hdet
    · ring
    · ring
    · linear_combination hdet
  · apply Units.ext
    rw [Units.val_mul, Units.val_neg, Units.val_one, hi, neg_one_fin2, Matrix.mul_fin_two]
    apply fin2_ext
    · linear_combination -hdet
    · ring
    · ring
    · linear_combination -hdet
  · apply Units.ext
    simp only [Units.val_mul, diagOne_fin2, diagOne_inv_fin2, hi, hsinv, Matrix.mul_fin_two]
    apply fin2_ext
    · apply mul_left_cancel₀ h3
      linear_combination ha2 - (τ : K) * hP3 - ha3
    · apply mul_left_cancel₀ h3
      linear_combination (b * (3 * a - 3 * (a + (τ : K)) * ((τ : K) - 1) + 2)) * ht2
        - (b * ((τ : K) + 2)) * ha3
    · apply mul_left_cancel₀ h3
      linear_combination (h.bar b) * ht2 + (h.bar b * ((τ : K) - 1)) * ha3
    · apply mul_left_cancel₀ h3
      linear_combination ((τ : K) ^ 3) * ha2 + ((τ : K) ^ 6) * ha3 - ((τ : K) ^ 2) * hP3
        - (4 * (τ : K) ^ 2 - (τ : K) - 1 + ((τ : K) - 1) ^ 2 * (1 + 2 * (τ : K)) *
          ((τ : K) ^ 2 + (τ : K) + 1)) * ht2
  · intro heq
    have hJ : ((diagOne τ * i₀ * (diagOne τ)⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
        !![a, b * (τ : K) ^ 2; -(h.bar b * (τ : K)), -(a * (τ : K) ^ 3)] := by
      simp only [Units.val_mul, diagOne_fin2, diagOne_inv_fin2, hi, hsinv, Matrix.mul_fin_two]
      apply fin2_ext <;> ring
    have h01 : (!![a, b * (τ : K) ^ 2; -(h.bar b * (τ : K)), -(a * (τ : K) ^ 3)] :
        Matrix (Fin 2) (Fin 2) K) 0 1 = (!![a, b; -h.bar b, -a] : Matrix (Fin 2) (Fin 2) K) 0 1 := by
      rw [← hJ, ← hi, heq]
    have h' : b * (τ : K) ^ 2 = b := h01
    have hb2 : b * ((τ : K) ^ 2 - 1) = 0 := by linear_combination h'
    have hτ2 : (τ : K) ^ 2 = 1 := by
      linear_combination (mul_eq_zero.mp hb2).resolve_left hb0
    have hτ' : (τ : K) = 1 := by linear_combination hτ3 - (τ : K) * hτ2
    exact hτ1 (Units.ext (by rw [Units.val_one]; exact hτ'))

end CFSG.RankThree.PartTwo.Sec14.Ronan148W
