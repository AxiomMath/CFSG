module

public import CFSG.Quasithin.Vol2.Ch6Sec1Lem4FusL3MxDefs
public import CFSG.GH74.GLS.IVK.Proofs2.Lemma41aU3

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin
open CFSG.GH74.GLS.IVK.Proofs2 CFSG.GH74.GLS.IVK.Proofs2.Lemma41aL3 CFSG.RankThree.SubgroupLists
open scoped Matrix

section Generic

variable {F : Type} [Field F]

private theorem u3inv_hs_mul (σ : F →+* F) (X Y : Matrix (Fin 2) (Fin 2) F) :
    ((X * Y).map σ)ᵀ = (Y.map σ)ᵀ * (X.map σ)ᵀ := by
  rw [Matrix.map_mul, Matrix.transpose_mul]

private theorem u3inv_hs_sub (σ : F →+* F) (X Y : Matrix (Fin 2) (Fin 2) F) :
    ((X - Y).map σ)ᵀ = (X.map σ)ᵀ - (Y.map σ)ᵀ := by
  ext i j
  simp

private theorem u3inv_hs_add (σ : F →+* F) (X Y : Matrix (Fin 2) (Fin 2) F) :
    ((X + Y).map σ)ᵀ = (X.map σ)ᵀ + (Y.map σ)ᵀ := by
  ext i j
  simp

private theorem u3inv_hs_smul (σ : F →+* F) (x : F) (hx : σ x = x)
    (X : Matrix (Fin 2) (Fin 2) F) : ((x • X).map σ)ᵀ = x • (X.map σ)ᵀ := by
  ext i j
  simp [hx]

private theorem u3inv_hs_one (σ : F →+* F) :
    ((1 : Matrix (Fin 2) (Fin 2) F).map σ)ᵀ = 1 := by
  rw [Matrix.map_one σ (map_zero σ) (map_one σ), Matrix.transpose_one]

private theorem u3inv_det_hs (σ : F →+* F) (X : Matrix (Fin 2) (Fin 2) F) :
    σ X.det = ((X.map σ)ᵀ).det := by
  rw [Matrix.det_transpose, RingHom.map_det, RingHom.mapMatrix_apply]

private theorem u3inv_mul_self (X : Matrix (Fin 2) (Fin 2) F) (hX : X.trace = 0) :
    X * X = (-X.det) • (1 : Matrix (Fin 2) (Fin 2) F) := by
  have h11 : X 1 1 = -X 0 0 := by
    have h := hX
    rw [Matrix.trace_fin_two] at h
    linear_combination h
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.det_fin_two, h11] <;> ring

private theorem u3inv_det_add_smul (C : Matrix (Fin 2) (Fin 2) F) (hC : C.trace = 0) (x : F) :
    (x • (1 : Matrix (Fin 2) (Fin 2) F) + C).det = x ^ 2 + C.det := by
  have h11 : C 1 1 = -C 0 0 := by
    have h := hC
    rw [Matrix.trace_fin_two] at h
    linear_combination h
  simp [Matrix.det_fin_two, h11]
  ring

private theorem u3inv_pow_succ (x : F) (C : Matrix (Fin 2) (Fin 2) F) (hC : C * C = 0) (n : ℕ) :
    (x • (1 : Matrix (Fin 2) (Fin 2) F) + C) ^ (n + 1) =
      x ^ (n + 1) • (1 : Matrix (Fin 2) (Fin 2) F) + (((n : F) + 1) * x ^ n) • C := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ih]
    simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one, smul_smul, hC,
      smul_zero, add_zero, zero_add]
    push_cast
    module

private theorem u3inv_star_eq_adj (σ : F →+* F) (M : Matrix (Fin 2) (Fin 2) F)
    (hU : (M.map σ)ᵀ * M = 1) (hdet : M.det = 1) : (M.map σ)ᵀ = M.adjugate := by
  calc (M.map σ)ᵀ = (M.map σ)ᵀ * (M * M.adjugate) := by
        rw [Matrix.mul_adjugate, hdet, one_smul, Matrix.mul_one]
    _ = ((M.map σ)ᵀ * M) * M.adjugate := (Matrix.mul_assoc _ _ _).symm
    _ = M.adjugate := by rw [hU, Matrix.one_mul]

private theorem u3inv_star_eq_sub (σ : F →+* F) (M : Matrix (Fin 2) (Fin 2) F)
    (hadj : (M.map σ)ᵀ = M.adjugate) :
    (M.map σ)ᵀ = (M 0 0 + M 1 1) • (1 : Matrix (Fin 2) (Fin 2) F) - M := by
  rw [hadj, Matrix.adjugate_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> ring

private theorem u3inv_star_entries (σ : F →+* F) (M : Matrix (Fin 2) (Fin 2) F)
    (hadj : (M.map σ)ᵀ = M.adjugate) :
    σ (M 0 0) = M 1 1 ∧ σ (M 1 1) = M 0 0 ∧ σ (M 0 1) = -M 1 0 ∧ σ (M 1 0) = -M 0 1 := by
  have e00 := congrArg (fun A : Matrix (Fin 2) (Fin 2) F => A 0 0) hadj
  have e01 := congrArg (fun A : Matrix (Fin 2) (Fin 2) F => A 0 1) hadj
  have e10 := congrArg (fun A : Matrix (Fin 2) (Fin 2) F => A 1 0) hadj
  have e11 := congrArg (fun A : Matrix (Fin 2) (Fin 2) F => A 1 1) hadj
  simp [Matrix.adjugate_fin_two] at e00 e01 e10 e11
  exact ⟨e00, e11, e10, e01⟩

private theorem u3inv_quadratic [Finite F] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (h : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData p 1 F) {s d : F}
    (hs : h.bar s = s) (hd : h.bar d = d) (hs0 : s ≠ 0) (hd0 : d ≠ 0) :
    ∃ a b : F, h.bar a = a ∧ h.bar b = b ∧ a ^ 2 - d * b ^ 2 = s⁻¹ := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : CharP F p := h.charP
  haveI : Fintype h.fixedField := Fintype.ofFinite _
  have hcard : Fintype.card h.fixedField % 2 = 1 := by
    obtain ⟨n, -, hn⟩ := FiniteField.card h.fixedField p
    rw [hn]
    exact Nat.odd_iff.mp (Odd.pow (hp.odd_of_ne_two hp2))
  let s₀ : h.fixedField := ⟨s, h.mem_fixedField.mpr hs⟩
  let d₀ : h.fixedField := ⟨d, h.mem_fixedField.mpr hd⟩
  have hd₀ : d₀ ≠ 0 := fun e => hd0 (congrArg Subtype.val e)
  have hf : (Polynomial.X ^ 2 - Polynomial.C s₀⁻¹ : Polynomial h.fixedField).degree = 2 :=
    Polynomial.degree_X_pow_sub_C (by norm_num) _
  have hg : (Polynomial.C (-d₀) * Polynomial.X ^ 2 : Polynomial h.fixedField).degree = 2 :=
    Polynomial.degree_C_mul_X_pow 2 (neg_ne_zero.mpr hd₀)
  obtain ⟨a₀, b₀, hab⟩ := FiniteField.exists_root_sum_quadratic hf hg hcard
  refine ⟨a₀, b₀, h.mem_fixedField.mp a₀.2, h.mem_fixedField.mp b₀.2, ?_⟩
  have key := congrArg Subtype.val hab
  simp [s₀, d₀] at key
  linear_combination key

end Generic

section Core

variable {F : Type} [Field F]

private theorem u3inv_core (σ : F →+* F) (hσ : ∀ x, σ (σ x) = x) (h2 : (2 : F) ≠ 0)
    (h5 : (5 : F) ≠ 0)
    (quad : ∀ s d : F, σ s = s → σ d = d → s ≠ 0 → d ≠ 0 →
      ∃ a b : F, σ a = a ∧ σ b = b ∧ a ^ 2 - d * b ^ 2 = s⁻¹)
    (M : Matrix (Fin 2) (Fin 2) F) (hU : (M.map σ)ᵀ * M = 1) (hdet : M.det = 1)
    (hM5 : M ^ 5 = 1) (hM1 : M ≠ 1) :
    ∃ R : Matrix (Fin 2) (Fin 2) F, (R.map σ)ᵀ = R ∧ R * R = 1 ∧ R.det = -1 ∧
      R * M * R = M⁻¹ := by
  have hadj := u3inv_star_eq_adj σ M hU hdet
  obtain ⟨s00, s11, s01, s10⟩ := u3inv_star_entries σ M hadj
  have hMs := u3inv_star_eq_sub σ M hadj
  obtain ⟨τ, hτ⟩ : ∃ τ : F, τ = M 0 0 + M 1 1 := ⟨_, rfl⟩
  rw [← hτ] at hMs
  have hστ : σ τ = τ := by rw [hτ, map_add, s00, s11, add_comm]
  obtain ⟨c₀, hc₀⟩ : ∃ c₀ : F, c₀ = (2 : F)⁻¹ * τ := ⟨_, rfl⟩
  have h2c₀ : 2 * c₀ = τ := by rw [hc₀, ← mul_assoc, mul_inv_cancel₀ h2, one_mul]
  have hσc₀ : σ c₀ = c₀ := by rw [hc₀, map_mul, map_inv₀, map_ofNat, hστ]
  obtain ⟨C, hC⟩ : ∃ C : Matrix (Fin 2) (Fin 2) F,
      C = M - c₀ • (1 : Matrix (Fin 2) (Fin 2) F) := ⟨_, rfl⟩
  have hMC : M = c₀ • (1 : Matrix (Fin 2) (Fin 2) F) + C := by rw [hC]; abel
  have htrM : M.trace = τ := by rw [Matrix.trace_fin_two, hτ]
  have hCtr : C.trace = 0 := by
    rw [hC, Matrix.trace_sub, htrM, Matrix.trace_smul, Matrix.trace_one, smul_eq_mul,
      Fintype.card_fin]
    push_cast
    linear_combination -h2c₀
  have hC11 : C 1 1 = -C 0 0 := by
    have h := hCtr
    rw [Matrix.trace_fin_two] at h
    linear_combination h
  have hsC : (C.map σ)ᵀ = -C := by
    rw [hC, u3inv_hs_sub σ, hMs, u3inv_hs_smul σ c₀ hσc₀, u3inv_hs_one σ, ← h2c₀]
    module
  have hMdet : c₀ ^ 2 + C.det = 1 := by
    have h := u3inv_det_add_smul C hCtr c₀
    rw [← hMC, hdet] at h
    exact h.symm
  obtain ⟨d, hd⟩ : ∃ d : F, d = -C.det := ⟨_, rfl⟩
  have hCC : C * C = d • (1 : Matrix (Fin 2) (Fin 2) F) := by
    rw [u3inv_mul_self C hCtr, hd]
  have hσd : σ d = d := by
    rw [hd, map_neg, u3inv_det_hs σ C, hsC, Matrix.det_neg]
    simp
  have hd0 : d ≠ 0 := by
    intro hd0
    have hC0 : C * C = 0 := by rw [hCC, hd0, zero_smul]
    have hpow : (c₀ • (1 : Matrix (Fin 2) (Fin 2) F) + C) ^ 5 =
        c₀ ^ 5 • (1 : Matrix (Fin 2) (Fin 2) F) + (5 * c₀ ^ 4) • C := by
      have h := u3inv_pow_succ c₀ C hC0 4
      rw [show ((4 : ℕ) : F) + 1 = 5 by norm_num] at h
      exact h
    rw [← hMC, hM5] at hpow
    have hc2 : c₀ ^ 2 = 1 := by linear_combination hMdet - hd + hd0
    have e00 := congrArg (fun A : Matrix (Fin 2) (Fin 2) F => A 0 0) hpow
    have e11 := congrArg (fun A : Matrix (Fin 2) (Fin 2) F => A 1 1) hpow
    simp [hC11] at e00 e11
    have hc5 : c₀ ^ 5 = 1 := by
      apply mul_left_cancel₀ h2
      linear_combination -e00 - e11
    have hz : (5 * c₀ ^ 4) • C = 0 := by
      have h' := hpow
      rw [hc5, one_smul] at h'
      exact add_left_cancel (h'.symm.trans (add_zero _).symm)
    rcases smul_eq_zero.mp hz with h54 | hC'
    · rcases mul_eq_zero.mp h54 with h5' | h4
      · exact h5 h5'
      · have hc0 : c₀ = 0 := by simpa using h4
        rw [hc0] at hc2
        norm_num at hc2
    · apply hM1
      have hc1 : c₀ = 1 := by linear_combination hc5 - c₀ * (c₀ ^ 2 + 1) * hc2
      rw [hMC, hC', add_zero, hc1, one_smul]
  have hC01 : C 0 1 = M 0 1 := by rw [hC]; simp
  have hC10 : C 1 0 = M 1 0 := by rw [hC]; simp
  obtain ⟨M₀, hM₀, hdetX⟩ : ∃ M₀ : Matrix (Fin 2) (Fin 2) F,
      (M₀.map σ)ᵀ = M₀ ∧ (M₀ * C - C * M₀).det ≠ 0 := by
    by_cases hb : M 0 1 = 0
    · have hc : M 1 0 = 0 := by
        have h := s01
        rw [hb, map_zero] at h
        linear_combination h
      have hx : C 0 0 ≠ 0 := by
        intro hx0
        apply hd0
        simp [hd, Matrix.det_fin_two, hC01, hC10, hC11, hx0, hb, hc]
      refine ⟨!![0, 1; 1, 0], ?_, ?_⟩
      · ext i j
        fin_cases i <;> fin_cases j <;> simp
      · have hX : (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) F) * C - C * !![0, 1; 1, 0] =
            !![0, -(2 * C 0 0); 2 * C 0 0, 0] := by
          ext i j
          simp only [Matrix.sub_apply, Matrix.mul_apply, Fin.sum_univ_two]
          fin_cases i <;> fin_cases j <;>
            simp [hC01, hC10, hC11, hb, hc] <;> ring
        rw [hX, Matrix.det_fin_two_of]
        intro h0
        exact mul_ne_zero (mul_ne_zero h2 hx) (mul_ne_zero h2 hx) (by linear_combination h0)
    · have hc : M 1 0 ≠ 0 := by
        intro hc0
        apply hb
        have h := hσ (M 0 1)
        rw [s01, hc0, neg_zero, map_zero] at h
        exact h.symm
      refine ⟨!![1, 0; 0, 0], ?_, ?_⟩
      · ext i j
        fin_cases i <;> fin_cases j <;> simp
      · have hX : (!![1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) F) * C - C * !![1, 0; 0, 0] =
            !![0, C 0 1; -C 1 0, 0] := by
          ext i j
          simp only [Matrix.sub_apply, Matrix.mul_apply, Fin.sum_univ_two]
          fin_cases i <;> fin_cases j <;> simp
        rw [hX, Matrix.det_fin_two_of, hC01, hC10]
        intro h0
        exact mul_ne_zero hb hc (by linear_combination h0)
  obtain ⟨X₁, hX₁⟩ : ∃ X : Matrix (Fin 2) (Fin 2) F, X = M₀ * C - C * M₀ := ⟨_, rfl⟩
  rw [← hX₁] at hdetX
  have hX₁tr : X₁.trace = 0 := by
    rw [hX₁, Matrix.trace_sub, Matrix.trace_mul_comm M₀ C, sub_self]
  have hX₁s : (X₁.map σ)ᵀ = X₁ := by
    rw [hX₁, u3inv_hs_sub σ, u3inv_hs_mul σ, u3inv_hs_mul σ, hM₀, hsC]
    noncomm_ring
  have hanti : C * X₁ + X₁ * C = 0 := by
    rw [hX₁]
    have e : C * (M₀ * C - C * M₀) + (M₀ * C - C * M₀) * C = M₀ * (C * C) - (C * C) * M₀ := by
      noncomm_ring
    rw [e, hCC]
    simp [Matrix.mul_smul, Matrix.smul_mul]
  have hCX₁ : C * X₁ = -(X₁ * C) := eq_neg_of_add_eq_zero_left hanti
  obtain ⟨X₂, hX₂⟩ : ∃ X : Matrix (Fin 2) (Fin 2) F, X = X₁ * C := ⟨_, rfl⟩
  have hX₂s : (X₂.map σ)ᵀ = X₂ := by
    rw [hX₂, u3inv_hs_mul σ, hsC, hX₁s, Matrix.neg_mul, hCX₁, neg_neg]
  have hX₂tr : X₂.trace = 0 := by
    have h1 := congrArg Matrix.trace hCX₁
    rw [Matrix.trace_mul_comm, Matrix.trace_neg] at h1
    have h3 : (2 : F) * (X₁ * C).trace = 0 := by linear_combination h1
    rw [hX₂]
    exact (mul_eq_zero.mp h3).resolve_left h2
  have hdetX₂ : X₂.det = X₁.det * C.det := by rw [hX₂, Matrix.det_mul]
  obtain ⟨s, hs⟩ : ∃ s : F, s = -X₁.det := ⟨_, rfl⟩
  have hσs : σ s = s := by rw [hs, map_neg, u3inv_det_hs σ X₁, hX₁s]
  have hs0 : s ≠ 0 := by rw [hs]; exact neg_ne_zero.mpr hdetX
  have hX₁X₁ : X₁ * X₁ = s • (1 : Matrix (Fin 2) (Fin 2) F) := by
    rw [u3inv_mul_self X₁ hX₁tr, hs]
  have hX₂X₂ : X₂ * X₂ = (-(s * d)) • (1 : Matrix (Fin 2) (Fin 2) F) := by
    rw [u3inv_mul_self X₂ hX₂tr, hdetX₂, hs, hd]
    congr 1
    ring
  have hX12 : X₁ * X₂ + X₂ * X₁ = 0 := by
    have e1 : X₁ * X₂ = s • C := by
      rw [hX₂, ← Matrix.mul_assoc, hX₁X₁, Matrix.smul_mul, Matrix.one_mul]
    have e2 : X₂ * X₁ = -(s • C) := by
      rw [hX₂, Matrix.mul_assoc, hCX₁, Matrix.mul_neg, ← Matrix.mul_assoc, hX₁X₁,
        Matrix.smul_mul, Matrix.one_mul]
    rw [e1, e2]
    abel
  obtain ⟨a, b, ha, hbσ, hab⟩ := quad s d hσs hσd hs0 hd0
  obtain ⟨R, hR⟩ : ∃ R : Matrix (Fin 2) (Fin 2) F, R = a • X₁ + b • X₂ := ⟨_, rfl⟩
  have hRs : (R.map σ)ᵀ = R := by
    rw [hR, u3inv_hs_add σ, u3inv_hs_smul σ a ha, u3inv_hs_smul σ b hbσ, hX₁s, hX₂s]
  have hRtr : R.trace = 0 := by
    rw [hR, Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul, hX₁tr, hX₂tr]
    simp
  have hRR : R * R = 1 := by
    have e : R * R = (a ^ 2 * s + b ^ 2 * (-(s * d))) • (1 : Matrix (Fin 2) (Fin 2) F) +
        (a * b) • (X₁ * X₂ + X₂ * X₁) := by
      rw [hR]
      simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
        hX₁X₁, hX₂X₂]
      module
    rw [e, hX12, smul_zero, add_zero]
    have hk : s * (a ^ 2 - d * b ^ 2) = 1 := by rw [hab, mul_inv_cancel₀ hs0]
    rw [show a ^ 2 * s + b ^ 2 * (-(s * d)) = s * (a ^ 2 - d * b ^ 2) by ring, hk, one_smul]
  have hRdet : R.det = -1 := by
    have h1 := u3inv_mul_self R hRtr
    rw [hRR] at h1
    have h00 := congrArg (fun A : Matrix (Fin 2) (Fin 2) F => A 0 0) h1
    simp at h00
    linear_combination h00
  have hX2C : X₂ * C = d • X₁ := by
    rw [hX₂, Matrix.mul_assoc, hCC, Matrix.mul_smul, Matrix.mul_one]
  have hCX2 : C * X₂ = -(d • X₁) := by
    rw [hX₂, ← Matrix.mul_assoc, hCX₁, Matrix.neg_mul, Matrix.mul_assoc, hCC, Matrix.mul_smul,
      Matrix.mul_one]
  have hRC : R * C = -(C * R) := by
    have e1 : R * C = a • X₂ + b • (d • X₁) := by
      rw [hR, Matrix.add_mul, Matrix.smul_mul, Matrix.smul_mul, ← hX₂, hX2C]
    have e2 : C * R = -(a • X₂ + b • (d • X₁)) := by
      rw [hR, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_smul, hCX₁, ← hX₂, hCX2]
      module
    rw [e1, e2, neg_neg]
  have hRCR : R * C * R = -C := by
    rw [hRC, Matrix.neg_mul, Matrix.mul_assoc, hRR, Matrix.mul_one]
  have hRMR : R * M * R = c₀ • (1 : Matrix (Fin 2) (Fin 2) F) - C := by
    rw [hMC, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul,
      hRR, hRCR, sub_eq_add_neg]
  have hinvM : (c₀ • (1 : Matrix (Fin 2) (Fin 2) F) - C) * M = 1 := by
    have e : (c₀ • (1 : Matrix (Fin 2) (Fin 2) F) - C) * (c₀ • 1 + C) =
        (c₀ ^ 2 - d) • (1 : Matrix (Fin 2) (Fin 2) F) := by
      simp only [Matrix.sub_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
        Matrix.mul_one, hCC]
      module
    have hc : c₀ ^ 2 - d = 1 := by rw [hd]; linear_combination hMdet
    rw [hMC, e, hc, one_smul]
  exact ⟨R, hRs, hRR, hRdet, by rw [hRMR, Matrix.inv_eq_left_inv hinvM]⟩

end Core

theorem exists_inverter_statedSU {F : Type} [Field F] [Finite F] {p : ℕ} (hp : p.Prime)
    (hp5 : 5 < p) (hF : Nat.card F = (p ^ 1) ^ 2) :
    ∀ B ∈ sl2Of (GU2Stated (p ^ 1) F), B ^ 5 = 1 → B ≠ 1 →
      ∃ R ∈ GU2Stated (p ^ 1) F, R * R = 1 ∧ (Matrix.GeneralLinearGroup.det R : Fˣ) = -1 ∧
        R * B * R⁻¹ = B⁻¹ := by
  intro B hB hB5 hB1
  let h : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData p 1 F :=
    ⟨hp, le_rfl, by rw [hF]; ring⟩
  haveI : CharP F p := h.charP
  have hp2 : p ≠ 2 := by omega
  have h2 : (2 : F) ≠ 0 := by
    intro h0
    have h0' : ((2 : ℕ) : F) = 0 := by exact_mod_cast h0
    rw [CharP.cast_eq_zero_iff F p] at h0'
    have := Nat.le_of_dvd (by norm_num) h0'
    omega
  have h5 : (5 : F) ≠ 0 := by
    intro h0
    have h0' : ((5 : ℕ) : F) = 0 := by exact_mod_cast h0
    rw [CharP.cast_eq_zero_iff F p] at h0'
    have := Nat.le_of_dvd (by norm_num) h0'
    omega
  rw [sl2Of, Subgroup.mem_inf, MonoidHom.mem_ker] at hB
  obtain ⟨hBG, hBdet⟩ := hB
  have hU := (CFSG.GH74.GLS.IVK.Proofs2.Lemma41aU3.mem_GU2Stated_iff h).mp hBG
  have hdetM : (B : Matrix (Fin 2) (Fin 2) F).det = 1 := by
    rw [← Matrix.GeneralLinearGroup.val_det_apply, hBdet, Units.val_one]
  have hM5 : (B : Matrix (Fin 2) (Fin 2) F) ^ 5 = 1 := by
    rw [← Units.val_pow_eq_pow_val, hB5, Units.val_one]
  have hM1 : (B : Matrix (Fin 2) (Fin 2) F) ≠ 1 :=
    fun e => hB1 (Units.ext (e.trans Units.val_one.symm))
  obtain ⟨R, hRs, hRR, hRdet, hRMR⟩ := u3inv_core h.bar h.bar_bar h2 h5
    (fun s d hs hd hs0 hd0 => u3inv_quadratic hp hp2 h hs hd hs0 hd0) _ hU hdetM hM5 hM1
  have hRRg : (⟨R, R, hRR, hRR⟩ : GL (Fin 2) F) * ⟨R, R, hRR, hRR⟩ = 1 := Units.ext hRR
  refine ⟨⟨R, R, hRR, hRR⟩,
    (CFSG.GH74.GLS.IVK.Proofs2.Lemma41aU3.mem_GU2Stated_iff h).mpr ?_, hRRg, ?_, ?_⟩
  · show (R.map h.bar)ᵀ * R = 1
    rw [hRs]
    exact hRR
  · apply Units.ext
    rw [Matrix.GeneralLinearGroup.val_det_apply, Units.val_neg, Units.val_one]
    exact hRdet
  · have hinv : (⟨R, R, hRR, hRR⟩ : GL (Fin 2) F)⁻¹ = ⟨R, R, hRR, hRR⟩ :=
      inv_eq_of_mul_eq_one_right hRRg
    rw [hinv]
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, Matrix.coe_units_inv]
    exact hRMR

end CFSG.Quasithin.H13
