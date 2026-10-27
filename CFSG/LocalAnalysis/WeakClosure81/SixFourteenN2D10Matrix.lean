module

public import CFSG.LocalAnalysis.WeakClosure81.SixFourteenN2F4Module

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open Matrix

theorem det_eq_scalar_of_order15
    (T : Matrix.GeneralLinearGroup (Fin 2) (GaloisField 2 2))
    (c : (GaloisField 2 2)ˣ)
    (hT15 : orderOf T = 15)
    (hT5 : T ^ 5 = Matrix.GeneralLinearGroup.scalar (Fin 2) c) :
    ((T : Matrix (Fin 2) (Fin 2) (GaloisField 2 2)).det = (c : GaloisField 2 2)) ∧
      orderOf c = 3 := by
  let K := GaloisField 2 2
  let δ : Kˣ := Matrix.GeneralLinearGroup.det T
  have hcardK : Nat.card K = 4 := by
    dsimp [K]
    rw [GaloisField.card 2 2 (by norm_num)]
    norm_num
  have hcardUnits : Nat.card Kˣ = 3 := by
    rw [Nat.card_units, hcardK]
  have hδ3u : δ ^ 3 = 1 := by
    have h := pow_card_eq_one' (x := δ)
    rwa [hcardUnits] at h
  have hδ5u : δ ^ 5 = c ^ 2 := by
    have h := congrArg (fun g : Matrix.GeneralLinearGroup (Fin 2) K =>
      Matrix.GeneralLinearGroup.det g) hT5
    rw [map_pow, Matrix.GeneralLinearGroup.det_scalar] at h
    simpa [δ] using h
  have hδ2u : δ ^ 2 = c ^ 2 := by
    have h5 : δ ^ 5 = δ ^ 2 := by
      rw [show (5 : ℕ) = 3 + 2 by norm_num, pow_add, hδ3u, one_mul]
    rw [← h5]
    exact hδ5u
  have hδ2 : (δ : K) ^ 2 = (c : K) ^ 2 := by
    have h := congrArg (fun u : Kˣ => (u : K)) hδ2u
    simpa using h
  have hδc : (δ : K) = (c : K) := by
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hδ2 with h | h
    · exact h
    · rwa [CharTwo.neg_eq] at h
  have hδu_eq_c : δ = c := Units.ext hδc
  have hδne : δ ≠ 1 := by
    intro hδ1
    have hc1 : c = 1 := by rw [← hδu_eq_c, hδ1]
    have hT5one : T ^ 5 = 1 := by simpa [hc1] using hT5
    have hdvd : orderOf T ∣ 5 := orderOf_dvd_iff_pow_eq_one.mpr hT5one
    rw [hT15] at hdvd
    norm_num at hdvd
  have hδorder : orderOf δ = 3 := by
    haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
    exact orderOf_eq_prime hδ3u hδne
  have hcorder : orderOf c = 3 := by
    rw [← hδu_eq_c]
    exact hδorder
  exact ⟨by simpa [δ] using hδc, hcorder⟩

theorem sq_modEq_one_of_twist_eq_pow
    (S T : Matrix.GeneralLinearGroup (Fin 2) (GaloisField 2 2)) (a : ℕ)
    (hT15 : orderOf T = 15)
    (hS : S * frobGL S = 1)
    (hphi : twist S T = T ^ a) :
    a * a ≡ 1 [MOD 15] := by
  have hfix : T = T ^ (a * a) := by
    calc T = twist S (twist S T) := (twist_involutive S hS T).symm
      _ = twist S (T ^ a) := by rw [hphi]
      _ = (twist S T) ^ a := by rw [map_pow]
      _ = (T ^ a) ^ a := by rw [hphi]
      _ = T ^ (a * a) := by rw [pow_mul]
  have hpow : T ^ (a * a) = T ^ 1 := by simpa using hfix.symm
  have h := (pow_eq_pow_iff_modEq (x := T) (n := a * a) (m := 1)).mp hpow
  simpa [hT15] using h

theorem no_twist_involution_on_order15_cyclic
    (S T : Matrix.GeneralLinearGroup (Fin 2) (GaloisField 2 2)) (a : ℕ)
    (c : (GaloisField 2 2)ˣ)
    (hT15 : orderOf T = 15)
    (hT5 : T ^ 5 = Matrix.GeneralLinearGroup.scalar (Fin 2) c)
    (hS : S * frobGL S = 1)
    (hphi : twist S T = T ^ a) :
    False := by
  let K := GaloisField 2 2
  letI : Fintype K := Fintype.ofFinite K
  let M : Matrix (Fin 2) (Fin 2) K := (T : Matrix (Fin 2) (Fin 2) K)
  let t : K := M.trace
  let d : K := M.det
  let δ : Kˣ := Matrix.GeneralLinearGroup.det T
  have hδval : (δ : K) = d := rfl
  have hdet := det_eq_scalar_of_order15 T c hT15 hT5
  have hdc : d = (c : K) := by simpa [d, δ, hδval] using hdet.1
  have hcorder : orderOf c = 3 := hdet.2
  have hc3 : c ^ 3 = 1 := by simpa [hcorder] using pow_orderOf_eq_one c
  have hd3 : d ^ 3 = 1 := by
    rw [hdc]
    simpa using congrArg (fun u : Kˣ => (u : K)) hc3
  have hδu_eq_c : δ = c := Units.ext (by simpa [hδval] using hdc)
  have hT5d : T ^ 5 = Matrix.GeneralLinearGroup.scalar (Fin 2) δ := by
    rw [hT5, ← hδu_eq_c]
  have hd0 : d ≠ 0 := by
    simpa [hδval] using δ.ne_zero
  have hcardK : Nat.card K = 4 := by
    dsimp [K]
    rw [GaloisField.card 2 2 (by norm_num)]
    norm_num
  have hmod15 : a * a ≡ 1 [MOD 15] :=
    sq_modEq_one_of_twist_eq_pow S T a hT15 hS hphi
  have hca : c ^ a = c ^ 2 := by
    have h1 : T ^ (5 * a) = Matrix.GeneralLinearGroup.scalar (Fin 2) (c ^ a) := by
      calc T ^ (5 * a) = (T ^ 5) ^ a := by rw [pow_mul]
        _ = (Matrix.GeneralLinearGroup.scalar (Fin 2) c) ^ a := by rw [hT5]
        _ = Matrix.GeneralLinearGroup.scalar (Fin 2) (c ^ a) := by rw [map_pow]
    have h2 : T ^ (5 * a) = Matrix.GeneralLinearGroup.scalar (Fin 2) (c ^ 2) := by
      calc T ^ (5 * a) = (T ^ a) ^ 5 := by
            rw [show 5 * a = a * 5 by ring, pow_mul]
        _ = (twist S T) ^ 5 := by rw [hphi]
        _ = twist S (T ^ 5) := by rw [map_pow]
        _ = twist S (Matrix.GeneralLinearGroup.scalar (Fin 2) c) := by rw [hT5]
        _ = Matrix.GeneralLinearGroup.scalar (Fin 2) (c ^ 2) := twist_scalar S c
    have hscalar : Matrix.GeneralLinearGroup.scalar (Fin 2) (c ^ a) =
        Matrix.GeneralLinearGroup.scalar (Fin 2) (c ^ 2) := h1.symm.trans h2
    apply Units.ext
    exact Matrix.scalar_inj.mp
      (congrArg (fun x : Matrix.GeneralLinearGroup (Fin 2) K =>
        (x : Matrix (Fin 2) (Fin 2) K)) hscalar)
  have hmod3 : a ≡ 2 [MOD 3] := by
    have h := (pow_eq_pow_iff_modEq (x := c) (n := a) (m := 2)).mp hca
    simpa [hcorder] using h
  have ha_mod : a % 15 = 11 ∨ a % 15 = 14 := by
    have h15a : (a * a) % 15 = 1 := by simpa [Nat.ModEq] using hmod15
    have h15 : (a % 15) * (a % 15) % 15 = 1 := by
      simpa [Nat.mul_mod] using h15a
    have h3a : a % 3 = 2 := by simpa [Nat.ModEq] using hmod3
    have h3 : (a % 15) % 3 = 2 := by
      rw [Nat.mod_mod_of_dvd a (by norm_num : 3 ∣ 15)]
      exact h3a
    have hr : a % 15 < 15 := Nat.mod_lt _ (by norm_num)
    have hcheck : ∀ r : Fin 15, ((r : ℕ) * (r : ℕ)) % 15 = 1 →
        (r : ℕ) % 3 = 2 → (r : ℕ) = 11 ∨ (r : ℕ) = 14 := by decide
    exact hcheck ⟨a % 15, hr⟩ h15 h3
  have hTa_pow : T ^ a = T ^ (a % 15) := by
    rw [← hT15]
    exact (pow_mod_orderOf T a).symm
  have hCH : M ^ 2 = t • M - d • 1 := by
    rw [pow_two]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.trace_fin_two, Matrix.det_fin_two,
        Matrix.sub_apply, Matrix.smul_apply, t, d] <;>
      ring
  have hCH2 : M ^ 2 = t • M + d • 1 := by
    simpa [sub_eq_add_neg, CharTwo.neg_eq] using hCH
  have h5gen : M ^ 5 = (t ^ 4 - 3 * t ^ 2 * d + d ^ 2) • M -
      (t ^ 3 * d - 2 * t * d ^ 2) • 1 := by
    have h5 : M ^ 5 = M ^ 2 * M ^ 2 * M := by
      rw [← pow_add, ← pow_succ]
    rw [h5, hCH]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.trace_fin_two, Matrix.det_fin_two,
        Matrix.sub_apply, Matrix.smul_apply, t, d] <;>
      ring
  have h5d_matrix : M ^ 5 = Matrix.scalar (Fin 2) d := by
    have h := congrArg (fun g : Matrix.GeneralLinearGroup (Fin 2) K =>
      (g : Matrix (Fin 2) (Fin 2) K)) hT5d
    simpa [M, d, hδval, Matrix.GeneralLinearGroup.coe_scalar] using h
  have htr5_formula : Matrix.trace (M ^ 5) =
      (t ^ 4 - 3 * t ^ 2 * d + d ^ 2) * t - 2 * (t ^ 3 * d - 2 * t * d ^ 2) := by
    have h := congrArg Matrix.trace h5gen
    rw [Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_smul, Matrix.trace_one,
      Fintype.card_fin] at h
    simpa [t, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using h
  have htr5_zero : Matrix.trace (M ^ 5) = 0 := by
    rw [h5d_matrix, Matrix.scalar_apply, Matrix.trace_diagonal]
    simp [Fin.sum_univ_two, CharTwo.add_self_eq_zero, CharTwo.two_eq_zero]
  have hαt : (t ^ 4 - 3 * t ^ 2 * d + d ^ 2) * t = 0 := by
    have h := htr5_formula
    rw [htr5_zero] at h
    simpa [CharTwo.two_eq_zero] using h.symm
  have ht0 : t ≠ 0 := by
    intro ht
    have hM2 : M ^ 2 = d • 1 := by simpa [ht] using hCH2
    have hM4 : M ^ 4 = d ^ 2 • 1 := by
      calc M ^ 4 = M ^ 2 * M ^ 2 := by
            rw [show (4 : ℕ) = 2 + 2 by norm_num, pow_add]
        _ = (d • 1) * (d • 1) := by rw [hM2]
        _ = d ^ 2 • 1 := by
            simp [Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_one, Matrix.one_mul,
              smul_smul, pow_two]
    have hM5 : M ^ 5 = d ^ 2 • M := by
      calc M ^ 5 = M ^ 4 * M := by
            rw [show (5 : ℕ) = 4 + 1 by norm_num, pow_add, pow_one]
        _ = (d ^ 2 • 1) * M := by rw [hM4]
        _ = d ^ 2 • M := by rw [Matrix.smul_mul, Matrix.one_mul]
    have hM5d : M ^ 5 = d • 1 := by
      rw [h5d_matrix, Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal]
    have hscalar : M = d ^ 2 • 1 := by
      have h : d ^ 2 • M = d • 1 := hM5.symm.trans hM5d
      calc M = (d * d ^ 2) • M := by
            rw [show d * d ^ 2 = d ^ 3 by ring, hd3, one_smul]
        _ = d • (d ^ 2 • M) := by rw [smul_smul]
        _ = d • (d • 1) := by rw [h]
        _ = (d * d) • 1 := by rw [smul_smul]
        _ = d ^ 2 • 1 := by rw [pow_two]
    have hM3 : M ^ 3 = 1 := by
      rw [hscalar, smul_pow]
      rw [show (d ^ 2) ^ 3 = (d ^ 3) ^ 2 by ring, hd3]
      simp
    have hT3 : T ^ 3 = 1 := by
      apply Units.ext
      simpa [M] using hM3
    have hdvd : orderOf T ∣ 3 := orderOf_dvd_iff_pow_eq_one.mpr hT3
    rw [hT15] at hdvd
    norm_num at hdvd
  have hαgen : t ^ 4 - 3 * t ^ 2 * d + d ^ 2 = 0 := by
    rcases mul_eq_zero.mp hαt with h | h
    · exact h
    · exact absurd h ht0
  have hα : t ^ 4 + d * t ^ 2 + d ^ 2 = 0 := by
    have h3 : (3 : K) = 1 := by
      have h := CharTwo.natCast_eq_ite (R := K) 3
      norm_num at h
      exact h
    rw [h3, CharTwo.sub_eq_add] at hαgen
    simp only [one_mul] at hαgen
    rwa [mul_comm (t ^ 2) d] at hαgen
  have ht4 : t ^ 4 = t := by
    have h := hroot_f4 t
    rw [← pow_mul] at h
    norm_num at h
    exact h
  have ht_poly : t + d * t ^ 2 + d ^ 2 = 0 := by
    simpa [ht4] using hα
  have htrace_frob : Matrix.trace
      (((frobGL T : Matrix.GeneralLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) =
      t ^ 2 := by
    rw [frobGL_coe, Matrix.trace_fin_two]
    rw [frobMatrixHom_apply, frobMatrixHom_apply]
    have ht_trace : t = M 0 0 + M 1 1 := by
      dsimp [t]
      rw [Matrix.trace_fin_two]
    rw [ht_trace, CharTwo.add_sq]
  have htrace_twist : Matrix.trace
      (((twist S T : Matrix.GeneralLinearGroup (Fin 2) K) :
        Matrix (Fin 2) (Fin 2) K)) = t ^ 2 := by
    have hmat : ((twist S T : Matrix.GeneralLinearGroup (Fin 2) K) :
        Matrix (Fin 2) (Fin 2) K) =
        (S : Matrix (Fin 2) (Fin 2) K) *
          ((frobGL T : Matrix.GeneralLinearGroup (Fin 2) K) :
            Matrix (Fin 2) (Fin 2) K) *
          ((S⁻¹ : Matrix.GeneralLinearGroup (Fin 2) K) :
            Matrix (Fin 2) (Fin 2) K) := by
      simpa using congrArg (fun g : Matrix.GeneralLinearGroup (Fin 2) K =>
        (g : Matrix (Fin 2) (Fin 2) K)) (twist_apply S T)
    rw [hmat, Matrix.trace_units_conj]
    exact htrace_frob
  have hcoe : ((T ^ a : Matrix.GeneralLinearGroup (Fin 2) K) :
      Matrix (Fin 2) (Fin 2) K) = M ^ a := by
    rfl
  have htrace_Ta : Matrix.trace (M ^ a) = t ^ 2 := by
    rw [← hcoe, ← hphi]
    exact htrace_twist
  have hT10_GL : T ^ 10 =
      Matrix.GeneralLinearGroup.scalar (Fin 2) (δ ^ 2) := by
    calc T ^ 10 = (T ^ 5) ^ 2 := by
          rw [show (10 : ℕ) = 5 * 2 by norm_num]
          exact pow_mul T 5 2
      _ = (Matrix.GeneralLinearGroup.scalar (Fin 2) δ) ^ 2 := by rw [hT5d]
      _ = Matrix.GeneralLinearGroup.scalar (Fin 2) (δ ^ 2) := by rw [map_pow]
  have hT10_matrix : ((T ^ 10 : Matrix.GeneralLinearGroup (Fin 2) K) :
      Matrix (Fin 2) (Fin 2) K) = Matrix.scalar (Fin 2) (d ^ 2) := by
    rw [hT10_GL, Matrix.GeneralLinearGroup.coe_scalar]
    rw [show ((δ ^ 2 : Kˣ) : K) = d ^ 2 by simp [hδval]]
  have hT11_matrix : ((T ^ 11 : Matrix.GeneralLinearGroup (Fin 2) K) :
      Matrix (Fin 2) (Fin 2) K) = Matrix.scalar (Fin 2) (d ^ 2) * M := by
    rw [show (11 : ℕ) = 10 + 1 by norm_num, pow_add, pow_one,
      Matrix.GeneralLinearGroup.coe_mul, hT10_matrix]
  have hT14_matrix : ((T ^ 14 : Matrix.GeneralLinearGroup (Fin 2) K) :
      Matrix (Fin 2) (Fin 2) K) = Matrix.scalar (Fin 2) (d ^ 2) * M ^ 4 := by
    have hT4_matrix : ((T ^ 4 : Matrix.GeneralLinearGroup (Fin 2) K) :
        Matrix (Fin 2) (Fin 2) K) = M ^ 4 := rfl
    rw [show (14 : ℕ) = 10 + 4 by norm_num, pow_add,
      Matrix.GeneralLinearGroup.coe_mul, hT10_matrix, hT4_matrix]
  have htrace_scalar_mul (u : K) (A : Matrix (Fin 2) (Fin 2) K) :
      Matrix.trace (Matrix.scalar (Fin 2) u * A) = u * Matrix.trace A := by
    rw [Matrix.scalar_apply, ← Matrix.smul_eq_diagonal_mul, Matrix.trace_smul]
    simp [smul_eq_mul]
  have ht4trace : Matrix.trace (M ^ 4) = t := by
    have hcard : Fintype.card K = 4 := by
      rw [← Nat.card_eq_fintype_card, hcardK]
    have h := FiniteField.trace_pow_card M
    rw [hcard] at h
    simpa [t, ht4] using h
  have ht_sq_eq : t ^ 2 = d ^ 2 * t := by
    rw [← htrace_Ta]
    rcases ha_mod with ha | ha
    · have hTa11 : T ^ a = T ^ 11 := by rw [hTa_pow, ha]
      calc Matrix.trace (M ^ a)
          = Matrix.trace (((T ^ a : Matrix.GeneralLinearGroup (Fin 2) K) :
              Matrix (Fin 2) (Fin 2) K)) := by rw [hcoe]
        _ = Matrix.trace (((T ^ 11 : Matrix.GeneralLinearGroup (Fin 2) K) :
              Matrix (Fin 2) (Fin 2) K)) := by rw [hTa11]
        _ = Matrix.trace (Matrix.scalar (Fin 2) (d ^ 2) * M) := by rw [hT11_matrix]
        _ = d ^ 2 * t := by rw [htrace_scalar_mul]
    · have hTa14 : T ^ a = T ^ 14 := by rw [hTa_pow, ha]
      calc Matrix.trace (M ^ a)
          = Matrix.trace (((T ^ a : Matrix.GeneralLinearGroup (Fin 2) K) :
              Matrix (Fin 2) (Fin 2) K)) := by rw [hcoe]
        _ = Matrix.trace (((T ^ 14 : Matrix.GeneralLinearGroup (Fin 2) K) :
              Matrix (Fin 2) (Fin 2) K)) := by rw [hTa14]
        _ = Matrix.trace (Matrix.scalar (Fin 2) (d ^ 2) * M ^ 4) := by rw [hT14_matrix]
        _ = d ^ 2 * Matrix.trace (M ^ 4) := htrace_scalar_mul (d ^ 2) (M ^ 4)
        _ = d ^ 2 * t := by rw [ht4trace]
  have ht_eq : t = d ^ 2 := by
    have h : t * t = t * d ^ 2 := by
      calc t * t = t ^ 2 := by ring
        _ = d ^ 2 * t := ht_sq_eq
        _ = t * d ^ 2 := by ring
    exact mul_left_cancel₀ ht0 h
  have hd4 : d ^ 4 = d := by
    have h := hroot_f4 d
    rw [← pow_mul] at h
    norm_num at h
    exact h
  have hcontra : d ^ 2 = 0 := by
    have h := ht_poly
    rw [ht_eq] at h
    rw [show (d ^ 2) ^ 2 = d ^ 4 by ring, hd4] at h
    rw [show d * d = d ^ 2 by ring] at h
    simpa [CharTwo.add_self_eq_zero] using h
  exact pow_ne_zero 2 hd0 hcontra

end CFSG.LocalAnalysis.WeakClosure81
