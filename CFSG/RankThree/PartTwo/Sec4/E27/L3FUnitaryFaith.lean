module

public import CFSG.RankThree.PartTwo.Sec4.E27.L3FUnitaryLine

public section

open CFSG.Open

namespace CFSG.RankThree.PartTwo.Sec4.E27

open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.RankThree.PartTwo.KFacts Matrix
open CFSG.RankThree.PartTwo.Sec19.Item19Res6Proof

section Matrices

variable {K : Type} [Field K]

theorem eq_one_of_conj_smul_trace {M N T : Matrix (Fin 3) (Fin 3) K} (hNM : N * M = 1) {c : K}
    (hc : M * T * N = c • T) (htr : Matrix.trace T ≠ 0) : c = 1 := by
  have ht := congrArg Matrix.trace hc
  rw [Matrix.trace_mul_comm (M * T) N, ← mul_assoc, hNM, one_mul, Matrix.trace_smul,
    smul_eq_mul] at ht
  have : (c - 1) * Matrix.trace T = 0 := by linear_combination -ht
  exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_right htr)

theorem mul_eq_mul_of_conj_eq' {M N T : Matrix (Fin 3) (Fin 3) K} (hNM : N * M = 1)
    (hc : M * T * N = T) : M * T = T * M := by
  calc M * T = M * T * (N * M) := by rw [hNM, mul_one]
    _ = M * T * N * M := by rw [mul_assoc (M * T) N M]
    _ = T * M := by rw [hc]

theorem trace_swapMat : Matrix.trace (swapMat K) = -1 := by
  simp [swapMat, Matrix.trace_fin_three]

theorem trace_swapMat' : Matrix.trace (swapMat' K) = -1 := by
  simp [swapMat', Matrix.trace_fin_three]

theorem swap_mul_diag_mul_swap {ω : K} (hω3 : ω ^ 3 = 1) :
    swapMat K * diagonal ![ω, ω ^ 2, 1] * swapMat K =
      diagonal ![ω, ω ^ 2, 1] * diagonal ![ω, ω ^ 2, 1] := by
  have h4 : ω ^ 2 * ω ^ 2 = ω := by
    calc ω ^ 2 * ω ^ 2 = ω ^ 3 * ω := by ring
      _ = ω := by rw [hω3, one_mul]
  ext i j
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal]
  fin_cases i <;> fin_cases j <;>
    simp [swapMat, Fin.sum_univ_three, Matrix.diagonal_apply, h4] <;> ring

theorem eq_one_of_conj_smul_diag {M N : Matrix (Fin 3) (Fin 3) K} (hNM : N * M = 1)
    (hMN : M * N = 1) {ω : K} (hω3 : ω ^ 3 = 1) (hS : M * swapMat K = swapMat K * M) {c : K}
    (hc : M * diagonal ![ω, ω ^ 2, 1] * N = c • diagonal ![ω, ω ^ 2, 1]) (hc0 : c ≠ 0) :
    c = 1 := by
  set D : Matrix (Fin 3) (Fin 3) K := diagonal ![ω, ω ^ 2, 1] with hD
  set S : Matrix (Fin 3) (Fin 3) K := swapMat K with hSdef
  have hS' : N * S = S * N := by
    calc N * S = N * S * (M * N) := by rw [hMN, mul_one]
      _ = N * (S * M) * N := by simp only [mul_assoc]
      _ = N * (M * S) * N := by rw [← hS]
      _ = (N * M) * S * N := by simp only [mul_assoc]
      _ = S * N := by rw [hNM, one_mul]
  have hsq : M * (D * D) * N = (M * D * N) * (M * D * N) := by
    calc M * (D * D) * N = M * D * (N * M) * D * N := by rw [hNM, mul_one]; simp only [mul_assoc]
      _ = (M * D * N) * (M * D * N) := by simp only [mul_assoc]
  have hSDS : S * D * S = D * D := swap_mul_diag_mul_swap hω3
  have h1 : M * (D * D) * N = c • (D * D) := by
    calc M * (D * D) * N = M * (S * D * S) * N := by rw [hSDS]
      _ = (M * S) * D * (S * N) := by simp only [mul_assoc]
      _ = (S * M) * D * (N * S) := by rw [hS, hS']
      _ = S * (M * D * N) * S := by simp only [mul_assoc]
      _ = S * (c • D) * S := by rw [hc]
      _ = c • (S * D * S) := by rw [Matrix.mul_smul, Matrix.smul_mul]
      _ = c • (D * D) := by rw [hSDS]
  have h2 : (c * c) • (D * D) = c • (D * D) := by
    rw [← h1, hsq, hc, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  have h3 := congrFun (congrFun h2 2) 2
  simp [hD, Matrix.smul_apply, Matrix.diagonal_apply] at h3
  exact mul_left_cancel₀ hc0 (by rw [mul_one]; exact h3)

theorem eq_smul_one_of_conj_smul {M N : Matrix (Fin 3) (Fin 3) K} (hNM : N * M = 1)
    (hMN : M * N = 1) {ω : K} (hω : IsPrimitiveRoot ω 3) {cE cE' cD : K}
    (hcE : M * swapMat K * N = cE • swapMat K) (hcE' : M * swapMat' K * N = cE' • swapMat' K)
    (hcD : M * diagonal ![ω, ω ^ 2, 1] * N = cD • diagonal ![ω, ω ^ 2, 1]) (hcD0 : cD ≠ 0) :
    M = M 0 0 • 1 := by
  have hcE1 : cE = 1 := eq_one_of_conj_smul_trace hNM hcE
    (by rw [trace_swapMat]; exact neg_ne_zero.2 one_ne_zero)
  have hcE1' : cE' = 1 := eq_one_of_conj_smul_trace hNM hcE'
    (by rw [trace_swapMat']; exact neg_ne_zero.2 one_ne_zero)
  rw [hcE1, one_smul] at hcE
  rw [hcE1', one_smul] at hcE'
  have h2 := mul_eq_mul_of_conj_eq' hNM hcE
  have h3 := mul_eq_mul_of_conj_eq' hNM hcE'
  have hcD1 : cD = 1 := eq_one_of_conj_smul_diag hNM hMN hω.pow_eq_one h2 hcD hcD0
  rw [hcD1, one_smul] at hcD
  have h1 := mul_eq_mul_of_conj_eq' hNM hcD
  exact Sec19.Item19Res6Proof.eq_smul_one_of_commute M hω h1 h2 h3

end Matrices

section Faithful

variable {p f : ℕ} {K : Type} [Field K]

theorem exists_smul_of_proj_eq (h : UnitaryFieldData p f K) {T g : unitarySU p f K 3}
    (hTg : unitaryProj h 3 T = unitaryProj h 3 g) :
    ∃ c : Kˣ, ((T : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      (c : K) • ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
  have h1 : g⁻¹ * T ∈ unitaryScalars h 3 := QuotientGroup.eq.1 hTg.symm
  obtain ⟨c, -, -, hc⟩ := h1
  refine ⟨c, ?_⟩
  have h2 : (T : GL (Fin 3) K) = (g : GL (Fin 3) K) * GeneralLinearGroup.scalar (Fin 3) c := by
    have := congrArg (fun x : GL (Fin 3) K => (g : GL (Fin 3) K) * x) hc
    simpa using this
  rw [h2, Units.val_mul, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
    ← Matrix.smul_one_eq_diagonal, Matrix.mul_smul, Matrix.mul_one]

theorem psuConj_eq_one_of_fixes (h : UnitaryFieldData p f K) (hQ : p ^ f % 3 = 2)
    (hq : 2 < p ^ f) {k : Subfield K} {σ : K ≃+* K} (hσ3 : σ ^ 3 = 1)
    (hk : ∀ x, x ∈ k ↔ σ x = x) {H B : unitaryIsom3 h}
    (hfix : ∀ g : unitarySU p f K 3,
      (∀ i j, ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) i j ∈ k) →
        psuConj h B (unitaryProj h 3 (suConj h H g)) = unitaryProj h 3 (suConj h H g)) :
    psuConj h B = 1 := by
  classical
  have := h.finite
  set M : unitaryIsom3 h := H⁻¹ * B * H with hM
  have hstep1 : ∀ g : unitarySU p f K 3,
      (∀ i j, ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) i j ∈ k) →
        unitaryProj h 3 (suConj h M g) = unitaryProj h 3 g := by
    intro g hg
    have h1 := hfix g hg
    rw [← psuConj_proj, hM, map_mul, map_mul, map_inv, MulAut.mul_apply, MulAut.mul_apply,
      psuConj_proj H, h1, ← psuConj_proj H]
    simp
  have hstep2 : ∀ g : unitarySU p f K 3,
      (∀ i j, ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) i j ∈ k) →
        ∃ c : Kˣ, ((M : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
          ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
          (((M : GL (Fin 3) K)⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
            (c : K) • ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
    intro g hg
    obtain ⟨c, hc⟩ := exists_smul_of_proj_eq h (hstep1 g hg)
    exact ⟨c, by simpa [coe_suConj] using hc⟩
  have hNM : (((M : GL (Fin 3) K)⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
      ((M : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = 1 := Units.inv_mul _
  have hMN : ((M : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
      (((M : GL (Fin 3) K)⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = 1 := Units.mul_inv _
  obtain ⟨gE, hgE⟩ : ∃ g : unitarySU p f K 3,
      ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = swapMat K :=
    ⟨⟨swapGL K, swapGL_mem_unitarySU h⟩, rfl⟩
  obtain ⟨gE', hgE'⟩ : ∃ g : unitarySU p f K 3,
      ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = swapMat' K :=
    ⟨⟨swapGL' K, swapGL'_mem_unitarySU h⟩, rfl⟩
  obtain ⟨cE, hcE⟩ := hstep2 gE (by intro i j; rw [hgE]; exact swapMat_mem i j)
  obtain ⟨cE', hcE'⟩ := hstep2 gE' (by intro i j; rw [hgE']; exact swapMat'_mem i j)
  rw [hgE] at hcE
  rw [hgE'] at hcE'
  have hK3 : 3 ∣ Nat.card K - 1 := by
    rw [h.card]
    have hpow : p ^ (2 * f) = (p ^ f) ^ 2 := by rw [pow_mul']
    rw [hpow]
    have h1 : (p ^ f) ^ 2 % 3 = 1 := by rw [Nat.pow_mod, hQ]
    have h2 : 1 ≤ (p ^ f) ^ 2 := Nat.one_le_pow _ _ (by omega)
    omega
  obtain ⟨ω, hω⟩ := Sec19.Item19Res5Proof.exists_isPrimitiveRoot_three hK3
  have hω3 : ω ^ 3 = 1 := hω.pow_eq_one
  have hωk : ω ∈ k := (hk ω).2 (ringEquiv_fix_of_cube hσ3 hω3)
  have hωN : h.norm ω = 1 := by
    rw [UnitaryFieldData.norm, bar_eq_of_cube h hQ hω3, ← pow_succ']
    exact hω3
  have hω2N : h.norm (ω ^ 2) = 1 := by
    rw [UnitaryFieldData.norm, map_pow, bar_eq_of_cube h hQ hω3, ← pow_mul, ← pow_add]
    calc ω ^ (2 + 2 * 2) = (ω ^ 3) ^ 2 := by ring
      _ = 1 := by rw [hω3, one_pow]
  obtain ⟨Dω, hDω⟩ := exists_diag_mem h ![ω, ω ^ 2, 1]
    (by
      intro i
      fin_cases i
      · exact hωN
      · exact hω2N
      · show h.norm 1 = 1
        simp [UnitaryFieldData.norm])
    (by
      show ω * ω ^ 2 * 1 = 1
      linear_combination hω3)
  have hDωk : ∀ i j, ((Dω : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) i j ∈ k := by
    intro i j
    rw [hDω]
    by_cases hij : i = j
    · subst hij
      fin_cases i <;> simp [hωk, k.one_mem, k.pow_mem hωk]
    · rw [diagonal_apply_ne _ hij]
      exact k.zero_mem
  obtain ⟨cD, hcD⟩ := hstep2 Dω hDωk
  rw [hDω] at hcD
  obtain ⟨c0, hMs⟩ : ∃ c0 : K, ((M : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      c0 • (1 : Matrix (Fin 3) (Fin 3) K) :=
    ⟨_, eq_smul_one_of_conj_smul hNM hMN hω hcE hcE' hcD cD.ne_zero⟩
  have hBm : ((B : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = c0 • 1 := by
    have e1 : (B : GL (Fin 3) K) = (H : GL (Fin 3) K) * (M : GL (Fin 3) K) *
        (H : GL (Fin 3) K)⁻¹ := by
      have : (M : GL (Fin 3) K) = (H : GL (Fin 3) K)⁻¹ * (B : GL (Fin 3) K) * (H : GL (Fin 3) K) :=
        rfl
      rw [this]
      group
    rw [e1, Units.val_mul, Units.val_mul, hMs, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul,
      Units.mul_inv]
  have hBcomm : ∀ X : GL (Fin 3) K, (B : GL (Fin 3) K) * X = X * (B : GL (Fin 3) K) := by
    intro X
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, hBm, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul,
      Matrix.mul_one]
  have hB1 : suConj h B = 1 := by
    refine MulEquiv.ext (fun x => ?_)
    apply Subtype.ext
    rw [MulAut.one_apply, coe_suConj, Subgroup.coe_inv, hBcomm, mul_inv_cancel_right]
  ext x
  induction x using QuotientGroup.induction_on with
  | H y => rw [MulAut.one_apply, psuConj_mk, hB1]; rfl

end Faithful

end CFSG.RankThree.PartTwo.Sec4.E27
