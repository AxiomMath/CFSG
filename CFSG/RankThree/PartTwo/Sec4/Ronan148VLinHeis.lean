module

public import CFSG.RankThree.PartTwo.Sec4.LThreePiHessian

public section

namespace CFSG.RankThree.PartTwo.Sec4.Ronan148V

open Matrix CFSG.RankThree.PartTwo.Sec4 CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.ComponentClassification

variable {F : Type} [Field F]

theorem conjAut_toGL (A : SpecialLinearGroup (Fin 3) F) :
    conjAut 3 F (Matrix.SpecialLinearGroup.toGL A) = MulAut.conj (proj 3 F A) := by
  ext u
  obtain ⟨g, rfl⟩ := proj_surjective 3 F u
  rw [conjAut_proj, MulAut.conj_apply, ← map_inv, ← map_mul, ← map_mul]
  congr 1
  apply Subtype.ext
  rw [coe_slConjugation, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  rfl

variable {τ : F}

theorem map_diagTau (hτ : τ ^ 3 = 1) (ρ : F ≃+* F) (hρ : ρ τ = τ) :
    GeneralLinearGroup.map (ρ : F →+* F) (diagTau hτ) = diagTau hτ := by
  apply Units.ext
  ext i j
  change (ρ : F →+* F) (((diagTau hτ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) i j) = _
  rw [coe_diagTau]
  fin_cases i <;> fin_cases j <;> simp [hρ]

theorem map_cycThree (ρ : F ≃+* F) :
    GeneralLinearGroup.map (ρ : F →+* F) cycThree = (cycThree : GL (Fin 3) F) := by
  apply Units.ext
  ext i j
  change (ρ : F →+* F) (((cycThree : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) i j) = _
  rw [coe_cycThree]
  fin_cases i <;> fin_cases j <;> simp

theorem map_fourierGL (h3 : (3 : F) ≠ 0) (hs : 1 + τ + τ ^ 2 = 0) (ρ : F ≃+* F) (hρ : ρ τ = τ) :
    GeneralLinearGroup.map (ρ : F →+* F) (fourierGL h3 hs) = fourierGL h3 hs := by
  apply Units.ext
  ext i j
  change (ρ : F →+* F) (((fourierGL h3 hs : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) i j) = _
  rw [coe_fourierGL]
  fin_cases i <;> fin_cases j <;> simp [fourierMat, hρ, map_inv₀]

theorem map_phaseGL (hτ : τ ^ 3 = 1) (ρ : F ≃+* F) (hρ : ρ τ = τ) :
    GeneralLinearGroup.map (ρ : F →+* F) (phaseGL hτ) = phaseGL hτ := by
  apply Units.ext
  ext i j
  change (ρ : F →+* F) (((phaseGL hτ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) i j) = _
  rw [coe_phaseGL]
  fin_cases i <;> fin_cases j <;> simp [hρ]

section Relations

variable (hτ : τ ^ 3 = 1) (h3 : (3 : F) ≠ 0) (hs : 1 + τ + τ ^ 2 = 0)

include hs in
theorem fourier_conj_diagTau (hτ0 : τ ≠ 0) :
    fourierGL h3 hs * diagTau hτ * (fourierGL h3 hs)⁻¹ =
      GeneralLinearGroup.scalar (Fin 3) (Units.mk0 τ hτ0) * cycThree⁻¹ := by
  have h : fourierGL h3 hs * diagTau hτ =
      GeneralLinearGroup.scalar (Fin 3) (Units.mk0 τ hτ0) * cycThree⁻¹ * fourierGL h3 hs := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, Units.val_mul, coe_fourierGL, coe_diagTau,
      coe_cycThree_inv, GeneralLinearGroup.coe_scalar, scalar_apply, Units.val_mk0]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [fourierMat, mul_apply, Fin.sum_univ_three, diagonal_apply] <;> grind
  rw [h]
  group

include hs in
theorem fourier_conj_cycThree (hτ0 : τ ≠ 0) :
    fourierGL h3 hs * cycThree * (fourierGL h3 hs)⁻¹ =
      GeneralLinearGroup.scalar (Fin 3) (Units.mk0 τ hτ0 ^ 2) * diagTau hτ := by
  have h : fourierGL h3 hs * cycThree =
      GeneralLinearGroup.scalar (Fin 3) (Units.mk0 τ hτ0 ^ 2) * diagTau hτ * fourierGL h3 hs := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, Units.val_mul, coe_fourierGL, coe_diagTau, coe_cycThree,
      GeneralLinearGroup.coe_scalar, scalar_apply, Units.val_pow_eq_pow_val, Units.val_mk0]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [fourierMat, mul_apply, Fin.sum_univ_three, diagonal_apply] <;> grind
  rw [h]
  group

theorem phase_conj_cycThree (hτ0 : τ ≠ 0) :
    phaseGL hτ * cycThree * (phaseGL hτ)⁻¹ =
      GeneralLinearGroup.scalar (Fin 3) (Units.mk0 τ hτ0) * (diagTau hτ * cycThree) := by
  have h : phaseGL hτ * cycThree =
      GeneralLinearGroup.scalar (Fin 3) (Units.mk0 τ hτ0) * (diagTau hτ * cycThree) *
        phaseGL hτ := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, Units.val_mul, Units.val_mul, coe_phaseGL, coe_diagTau,
      coe_cycThree, GeneralLinearGroup.coe_scalar, scalar_apply, Units.val_mk0]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [mul_apply, Fin.sum_univ_three, diagonal_apply] <;> grind
  rw [h]
  group

theorem phase_mul_diagTau : phaseGL hτ * diagTau hτ = diagTau hτ * phaseGL hτ := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, coe_phaseGL, coe_diagTau]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [mul_apply, Fin.sum_univ_three]

end Relations

theorem exists_lam_linear [Finite F] {n : ℕ} (hn : 1 ≤ n) (hF : Nat.card F = 2 ^ (3 * n))
    (hq : 2 ^ (3 * n) % 3 = 1) {ρ : F ≃+* F} (hρ : orderOf ρ = 3) :
    ∃ m : ℕ, Nat.Coprime m 3 ∧ ∃ lam : Fˣ, lam ^ m = 1 ∧ ρ lam ≠ lam := by
  set q := 2 ^ n with hqdef
  have hq3 : q % 3 = 1 := by
    have h1 : (2 : ℕ) ^ (3 * n) = q ^ 3 := by rw [hqdef, ← pow_mul, mul_comm]
    rw [h1, Nat.pow_mod] at hq
    have : q % 3 < 3 := Nat.mod_lt _ (by norm_num)
    interval_cases h : q % 3 <;> simp_all
  have hq1 : 2 ≤ q := by
    have : 2 ^ 1 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    simpa [hqdef] using this
  obtain ⟨t, ht⟩ : ∃ t, q = 3 * t + 1 := ⟨q / 3, by omega⟩
  set m := 3 * t ^ 2 + 3 * t + 1 with hm
  have hm3 : Nat.Coprime m 3 := by
    rw [Nat.Coprime, Nat.gcd_comm, Nat.gcd_rec]
    have : m % 3 = 1 := by omega
    rw [this]
    rfl
  have hqm : q ^ 2 + q + 1 = 3 * m := by rw [ht, hm]; ring
  have hQ : 2 ^ (3 * n) - 1 = (q - 1) * (3 * m) := by
    have h1 : (2 : ℕ) ^ (3 * n) = q ^ 3 := by rw [hqdef, ← pow_mul, mul_comm]
    rw [h1, ← hqm]
    have : 1 ≤ q := by omega
    zify [Nat.one_le_pow 3 q this, this]
    ring
  have := Fintype.ofFinite F
  obtain ⟨γ, hγ⟩ := IsCyclic.exists_generator (α := Fˣ)
  have hγo : orderOf γ = 2 ^ (3 * n) - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hγ, Nat.card_units, hF]
  have hdvd : m ∣ 2 ^ (3 * n) - 1 := by
    rw [hQ]
    exact ⟨(q - 1) * 3, by ring⟩
  obtain ⟨k, hk⟩ := hdvd
  set lam := γ ^ k with hlam
  have hk0 : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h | h
    · exfalso
      rw [h, mul_zero] at hk
      have : 2 ≤ 2 ^ (3 * n) := Nat.le_self_pow (by omega) 2
      omega
    · exact h
  have hlo : orderOf lam = m := by
    rw [hlam, orderOf_pow_of_dvd hk0.ne' ⟨m, by rw [hγo, hk, mul_comm]⟩, hγo, hk,
      Nat.mul_div_cancel _ hk0]
  refine ⟨m, hm3, lam, by rw [← hlo, pow_orderOf_eq_one], fun hfix => ?_⟩
  obtain ⟨-, hρ'⟩ := KFacts.eq_frobenius_pow_of_orderOf_eq_three Nat.prime_two (by omega) hF hρ
  have hn3 : 3 * n / 3 = n := by omega
  have hn6 : 2 * (3 * n) / 3 = 2 * n := by omega
  rw [hn3, hn6] at hρ'
  have hmq : m ∣ q - 1 := by
    rcases hρ' with h | h
    · have h1 : (lam : F) ^ q = lam := by rw [← h, hfix]
      have h2 : lam ^ (q - 1) = 1 := by
        apply Units.ext
        rw [Units.val_pow_eq_pow_val, Units.val_one]
        have := lam.ne_zero
        have h3 : (lam : F) ^ (q - 1) * lam = 1 * lam := by
          rw [← pow_succ, Nat.sub_add_cancel (by omega), h1, one_mul]
        exact mul_right_cancel₀ this h3
      rw [← hlo]
      exact orderOf_dvd_of_pow_eq_one h2
    · have h1 : (lam : F) ^ (q ^ 2) = lam := by
        have hq2 : q ^ 2 = 2 ^ (2 * n) := by rw [hqdef, ← pow_mul, mul_comm]
        rw [hq2, ← h, hfix]
      have h2 : lam ^ (q ^ 2 - 1) = 1 := by
        apply Units.ext
        rw [Units.val_pow_eq_pow_val, Units.val_one]
        have := lam.ne_zero
        have h3 : (lam : F) ^ (q ^ 2 - 1) * lam = 1 * lam := by
          rw [← pow_succ, Nat.sub_add_cancel (Nat.one_le_pow _ _ (by omega)), h1, one_mul]
        exact mul_right_cancel₀ this h3
      have h4 : m ∣ q ^ 2 - 1 := by
        rw [← hlo]
        exact orderOf_dvd_of_pow_eq_one h2
      have h5 : m ∣ q ^ 3 - 1 := by
        have h6 : (2 : ℕ) ^ (3 * n) = q ^ 3 := by rw [hqdef, ← pow_mul, mul_comm]
        rw [← h6, hQ]
        exact ⟨(q - 1) * 3, by ring⟩
      have h8 : q * (q ^ 2 - 1) = q ^ 3 - q := by
        rw [Nat.mul_sub_one, ← pow_succ']
      have h9 := Nat.dvd_sub h5 (Dvd.dvd.mul_left h4 q)
      rw [h8] at h9
      have hqq : q ≤ q ^ 3 := Nat.le_self_pow (by norm_num) q
      have e : q ^ 3 - 1 - (q ^ 3 - q) = q - 1 := by omega
      rwa [e] at h9
  have hle := Nat.le_of_dvd (by omega) hmq
  have e : q - 1 = 3 * t := by omega
  rw [e, hm] at hle
  nlinarith

end CFSG.RankThree.PartTwo.Sec4.Ronan148V
