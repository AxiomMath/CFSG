module

public import CFSG.RankThree.PartTwo.Sec21.Item211Lie3ProofSpBlocks

public section

namespace CFSG.RankThree.PartTwo.Sec21

namespace Item211Lie3Proof

open Matrix CFSG.Assembly.LowTwoRank
open CFSG.RankThree.SubgroupLists (spGram)

local notation "V₄" => Fin 2 ⊕ Fin 2

variable {K : Type} [Field K]

@[expose] noncomputable def xiMat (P S : Matrix (Fin 2) (Fin 2) K) : Matrix V₄ V₄ K :=
  Matrix.fromBlocks !![P 0 0, -3 * S 0 0; S 0 0, P 0 0] !![P 0 1, -S 0 1; S 0 1, P 0 1 / 3]
    !![P 1 0, -3 * S 1 0; 3 * S 1 0, 3 * P 1 0] !![P 1 1, -S 1 1; 3 * S 1 1, P 1 1]

@[expose] noncomputable def jStd : Matrix V₄ V₄ K := xiMat 0 1

theorem xiMat_mul (h3 : (3 : K) ≠ 0) (P S P' S' : Matrix (Fin 2) (Fin 2) K) :
    xiMat P S * xiMat P' S' = xiMat (P * P' - (3 : K) • (S * S')) (P * S' + S * P') := by
  ext i k
  rcases i with i | i <;> rcases k with k | k <;> fin_cases i <;> fin_cases k <;>
    simp [xiMat, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, Matrix.fromBlocks] <;>
    field_simp <;> ring

theorem xiMat_smul_one (c : K) : xiMat (c • (1 : Matrix (Fin 2) (Fin 2) K)) 0 = c • 1 := by
  ext i k
  rcases i with i | i <;> rcases k with k | k <;> fin_cases i <;> fin_cases k <;>
    simp [xiMat, Matrix.fromBlocks]

theorem xiMat_one : xiMat (1 : Matrix (Fin 2) (Fin 2) K) 0 = 1 := by
  simpa using xiMat_smul_one (1 : K)

theorem xiMat_neg (P S : Matrix (Fin 2) (Fin 2) K) : xiMat (-P) (-S) = -xiMat P S := by
  ext i k
  rcases i with i | i <;> rcases k with k | k <;> fin_cases i <;> fin_cases k <;>
    simp [xiMat, Matrix.fromBlocks] <;> ring

theorem xiMat_injective (h3 : (3 : K) ≠ 0) {P S P' S' : Matrix (Fin 2) (Fin 2) K}
    (h : xiMat P S = xiMat P' S') : P = P' ∧ S = S' := by
  have e : ∀ i k, xiMat P S i k = xiMat P' S' i k := fun i k => by rw [h]
  have e1 := e (Sum.inl 0) (Sum.inl 0)
  have e2 := e (Sum.inl 0) (Sum.inr 0)
  have e3 := e (Sum.inr 0) (Sum.inl 0)
  have e4 := e (Sum.inr 0) (Sum.inr 0)
  have e5 := e (Sum.inl 1) (Sum.inl 0)
  have e6 := e (Sum.inl 1) (Sum.inr 0)
  have e7 := e (Sum.inr 1) (Sum.inl 0)
  have e8 := e (Sum.inr 1) (Sum.inr 0)
  simp [xiMat, Matrix.fromBlocks] at e1 e2 e3 e4 e5 e6 e7 e8
  replace e7 := e7.resolve_right h3
  replace e8 := e8.resolve_right h3
  refine ⟨?_, ?_⟩ <;> ext a b <;> fin_cases a <;> fin_cases b <;> simp_all

theorem xiMat_scalar_comm (h3 : (3 : K) ≠ 0) (α β : K) (P S : Matrix (Fin 2) (Fin 2) K) :
    xiMat (α • 1) (β • 1) * xiMat P S = xiMat P S * xiMat (α • 1) (β • 1) := by
  rw [xiMat_mul h3, xiMat_mul h3]
  congr 1
  · simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one]
  · simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one]
    abel

theorem xiMat_commute_jStd (h3 : (3 : K) ≠ 0) (P S : Matrix (Fin 2) (Fin 2) K) :
    xiMat P S * jStd = jStd * xiMat P S := by
  have e := xiMat_scalar_comm h3 0 1 P S
  rw [zero_smul, one_smul] at e
  have e0 : xiMat (0 : Matrix (Fin 2) (Fin 2) K) 1 = jStd := rfl
  rw [e0] at e
  exact e.symm

theorem eq_xiMat_of_commute (h3 : (3 : K) ≠ 0) {N : Matrix V₄ V₄ K}
    (hN : N * jStd = jStd * N) :
    N = xiMat !![N (Sum.inl 0) (Sum.inl 0), N (Sum.inl 0) (Sum.inr 0);
        N (Sum.inr 0) (Sum.inl 0), N (Sum.inr 0) (Sum.inr 0)]
      !![N (Sum.inl 1) (Sum.inl 0), N (Sum.inl 1) (Sum.inr 0);
        N (Sum.inr 1) (Sum.inl 0) / 3, N (Sum.inr 1) (Sum.inr 0) / 3] := by
  have e : ∀ i k, (N * jStd : Matrix V₄ V₄ K) i k = (jStd * N : Matrix V₄ V₄ K) i k :=
    fun i k => by rw [hN]
  have c1 := e (Sum.inl 0) (Sum.inl 0)
  have c2 := e (Sum.inr 0) (Sum.inl 0)
  have c3 := e (Sum.inr 1) (Sum.inl 0)
  have c4 := e (Sum.inl 0) (Sum.inr 0)
  have c5 := e (Sum.inl 1) (Sum.inr 0)
  have c6 := e (Sum.inr 0) (Sum.inr 0)
  have c7 := e (Sum.inr 1) (Sum.inr 0)
  have c8 := e (Sum.inl 1) (Sum.inl 0)
  simp [jStd, xiMat, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two,
    Matrix.fromBlocks] at c1 c2 c3 c4 c5 c6 c7 c8
  have d2 : N (Sum.inr 0) (Sum.inl 1) = -3 * (N (Sum.inr 1) (Sum.inl 0) / 3) := by
    rw [c2]
    field_simp
  have d4 : N (Sum.inl 0) (Sum.inr 1) = -N (Sum.inl 1) (Sum.inr 0) :=
    mul_right_cancel₀ h3 (by rw [c4]; ring)
  have d5 : N (Sum.inl 1) (Sum.inr 1) = N (Sum.inl 0) (Sum.inr 0) / 3 := by
    rw [eq_div_iff h3]
    exact c5
  have d6 : N (Sum.inr 0) (Sum.inr 1) = -(N (Sum.inr 1) (Sum.inr 0) / 3) := by
    field_simp
    linear_combination c6
  have d7 : N (Sum.inr 1) (Sum.inr 1) = N (Sum.inr 0) (Sum.inr 0) :=
    mul_right_cancel₀ h3 (by rw [c7]; ring)
  have e9 : N (Sum.inr 1) (Sum.inl 0) = 3 * (N (Sum.inr 1) (Sum.inl 0) / 3) := by
    field_simp
  have e10 : N (Sum.inr 1) (Sum.inr 0) = 3 * (N (Sum.inr 1) (Sum.inr 0) / 3) := by
    field_simp
  ext i k
  rcases i with i | i <;> rcases k with k | k <;> fin_cases i <;> fin_cases k <;>
    simp [xiMat, Matrix.fromBlocks] <;>
    first
    | linear_combination c1 | linear_combination d2 | linear_combination c3
    | linear_combination d4 | linear_combination d5 | linear_combination d6
    | linear_combination d7 | linear_combination c8 | linear_combination e9
    | linear_combination e10

theorem star_xiMat (P S : Matrix (Fin 2) (Fin 2) K) :
    -(spGram 2 K * (xiMat P S)ᵀ * spGram 2 K) = xiMat (adjugate P) (-adjugate S) := by
  ext i k
  rcases i with i | i <;> rcases k with k | k <;> fin_cases i <;> fin_cases k <;>
    simp [xiMat, spGram, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two,
      Matrix.fromBlocks, adjugate_fin_two] <;> ring

@[expose] noncomputable def rSc (α β : K) : Matrix V₄ V₄ K :=
  xiMat (α • (1 : Matrix (Fin 2) (Fin 2) K)) (β • 1)

theorem rSc_mul (h3 : (3 : K) ≠ 0) (α β α' β' : K) :
    rSc α β * rSc α' β' = rSc (α * α' - 3 * (β * β')) (α * β' + β * α') := by
  rw [rSc, rSc, xiMat_mul h3, rSc]
  congr 1 <;> ext a b <;> fin_cases a <;> fin_cases b <;> simp <;> ring

theorem rSc_mul_xiMat (h3 : (3 : K) ≠ 0) (α β : K) (M : Matrix (Fin 2) (Fin 2) K) :
    rSc α β * xiMat M 0 = xiMat (α • M) (β • M) := by
  rw [rSc, xiMat_mul h3]
  congr 1
  · simp
  · simp

theorem xiMat_mul_xiMat_zero (h3 : (3 : K) ≠ 0) (M M' : Matrix (Fin 2) (Fin 2) K) :
    xiMat M 0 * xiMat M' 0 = xiMat (M * M') 0 := by
  rw [xiMat_mul h3]
  congr 1 <;> simp

theorem rSc_comm (h3 : (3 : K) ≠ 0) (α β : K) (P S : Matrix (Fin 2) (Fin 2) K) :
    rSc α β * xiMat P S = xiMat P S * rSc α β :=
  xiMat_scalar_comm h3 α β P S

theorem eq_smul_one_of_eq_adjugate (h2 : (2 : K) ≠ 0) {W : Matrix (Fin 2) (Fin 2) K}
    (h : W = adjugate W) : W = W 0 0 • (1 : Matrix (Fin 2) (Fin 2) K) := by
  have e : ∀ a b, W a b = adjugate W a b := fun a b => by rw [← h]
  have e01 := e 0 1
  have e10 := e 1 0
  have e11 := e 1 1
  simp [adjugate_fin_two] at e01 e10 e11
  have z01 : W 0 1 = 0 := by
    have : (2 : K) * W 0 1 = 0 := by linear_combination e01
    exact (mul_eq_zero.mp this).resolve_left h2
  have z10 : W 1 0 = 0 := by
    have : (2 : K) * W 1 0 = 0 := by linear_combination e10
    exact (mul_eq_zero.mp this).resolve_left h2
  ext a b
  fin_cases a <;> fin_cases b <;> simp [z01, z10, e11]

theorem exists_smul_of_adjugate (h2 : (2 : K) ≠ 0) {P S : Matrix (Fin 2) (Fin 2) K}
    (hdet : P.det + 3 * S.det ≠ 0) (h : adjugate P * S = adjugate S * P) :
    ∃ (α β : K) (M : Matrix (Fin 2) (Fin 2) K), P = α • M ∧ S = β • M := by
  by_cases hP : P.det = 0
  · have hS : S.det ≠ 0 := by
      intro h0
      apply hdet
      rw [hP, h0, mul_zero, add_zero]
    have e1 : S * adjugate P * (S * adjugate S) = S * adjugate S * (P * adjugate S) := by
      calc S * adjugate P * (S * adjugate S) = S * (adjugate P * S) * adjugate S := by
            simp only [Matrix.mul_assoc]
        _ = S * (adjugate S * P) * adjugate S := by rw [h]
        _ = S * adjugate S * (P * adjugate S) := by simp only [Matrix.mul_assoc]
    rw [mul_adjugate, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, Matrix.one_mul] at e1
    have e2 : S * adjugate P = P * adjugate S := smul_right_injective _ hS e1
    have hW : P * adjugate S = adjugate (P * adjugate S) := by
      rw [adjugate_mul_distrib, adjugate_adjugate', Fintype.card_fin, Nat.sub_self, pow_zero,
        one_smul, ← e2]
    have hsc := eq_smul_one_of_eq_adjugate h2 hW
    refine ⟨(P * adjugate S) 0 0 / S.det, 1, S, ?_, by rw [one_smul]⟩
    have e3 : P * adjugate S * S = ((P * adjugate S) 0 0 • (1 : Matrix (Fin 2) (Fin 2) K)) * S := by
      rw [← hsc]
    rw [Matrix.mul_assoc, adjugate_mul, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul,
      Matrix.one_mul] at e3
    rw [div_eq_inv_mul, ← smul_smul, ← e3, smul_smul, inv_mul_cancel₀ hS, one_smul]
  ·
    have e1 : P * adjugate P * (S * adjugate P) = P * adjugate S * (P * adjugate P) := by
      calc P * adjugate P * (S * adjugate P) = P * (adjugate P * S) * adjugate P := by
            simp only [Matrix.mul_assoc]
        _ = P * (adjugate S * P) * adjugate P := by rw [h]
        _ = P * adjugate S * (P * adjugate P) := by simp only [Matrix.mul_assoc]
    rw [mul_adjugate, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul, Matrix.mul_one] at e1
    have e2 : S * adjugate P = P * adjugate S := smul_right_injective _ hP e1
    have hW : S * adjugate P = adjugate (S * adjugate P) := by
      rw [adjugate_mul_distrib, adjugate_adjugate', Fintype.card_fin, Nat.sub_self, pow_zero,
        one_smul, e2]
    have hsc := eq_smul_one_of_eq_adjugate h2 hW
    refine ⟨1, (S * adjugate P) 0 0 / P.det, P, by rw [one_smul], ?_⟩
    have e3 : S * adjugate P * P = ((S * adjugate P) 0 0 • (1 : Matrix (Fin 2) (Fin 2) K)) * P := by
      rw [← hsc]
    rw [Matrix.mul_assoc, adjugate_mul, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul,
      Matrix.one_mul] at e3
    rw [div_eq_inv_mul, ← smul_smul, ← e3, smul_smul, inv_mul_cancel₀ hP, one_smul]

theorem spGram_mul_self : spGram 2 K * spGram 2 K = -(1 : Matrix V₄ V₄ K) := by
  ext i k
  rcases i with i | i <;> rcases k with k | k <;> fin_cases i <;> fin_cases k <;>
    simp [spGram, Matrix.fromBlocks, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply]

theorem exists_xi_decomp (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0) {N : Matrix V₄ V₄ K} {μ : K}
    (hμ : μ ≠ 0) (hN : N * jStd = jStd * N) (hsim : Nᵀ * spGram 2 K * N = μ • spGram 2 K) :
    ∃ (α β : K) (M : Matrix (Fin 2) (Fin 2) K), N = rSc α β * xiMat M 0 ∧
      (α ^ 2 + 3 * β ^ 2) * M.det = μ := by
  set P := !![N (Sum.inl 0) (Sum.inl 0), N (Sum.inl 0) (Sum.inr 0);
    N (Sum.inr 0) (Sum.inl 0), N (Sum.inr 0) (Sum.inr 0)] with hP
  set S := !![N (Sum.inl 1) (Sum.inl 0), N (Sum.inl 1) (Sum.inr 0);
    N (Sum.inr 1) (Sum.inl 0) / 3, N (Sum.inr 1) (Sum.inr 0) / 3] with hS
  have hNx : N = xiMat P S := eq_xiMat_of_commute h3 hN
  have hstar : xiMat (adjugate P) (-adjugate S) * xiMat P S = xiMat (μ • 1) 0 := by
    rw [← star_xiMat, ← hNx, xiMat_smul_one]
    calc -(spGram 2 K * Nᵀ * spGram 2 K) * N = -(spGram 2 K * (Nᵀ * spGram 2 K * N)) := by
          simp only [Matrix.neg_mul, Matrix.mul_assoc]
      _ = μ • 1 := by
          rw [hsim, Matrix.mul_smul, spGram_mul_self, smul_neg, neg_neg]
  rw [xiMat_mul h3] at hstar
  obtain ⟨e1, e2⟩ := xiMat_injective h3 hstar
  rw [adjugate_mul, Matrix.neg_mul, adjugate_mul, smul_neg, sub_neg_eq_add, smul_smul,
    ← add_smul] at e1
  have hdet : P.det + 3 * S.det = μ := by
    have e := congrFun (congrFun e1 0) 0
    simpa using e
  rw [Matrix.neg_mul, ← sub_eq_add_neg, sub_eq_zero] at e2
  obtain ⟨α, β, M, hPM, hSM⟩ := exists_smul_of_adjugate h2 (by rw [hdet]; exact hμ) e2
  refine ⟨α, β, M, by rw [hNx, hPM, hSM, rSc_mul_xiMat h3], ?_⟩
  rw [← hdet, hPM, hSM, Matrix.det_smul, Matrix.det_smul, Fintype.card_fin]
  ring

theorem exists_xi_decomp_three (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0) {N : Matrix V₄ V₄ K}
    (hN : N * jStd = jStd * N) (hsp : Nᵀ * spGram 2 K * N = spGram 2 K) (hN3 : N * N * N = 1) :
    ∃ (α β : K) (X : Matrix (Fin 2) (Fin 2) K), N = rSc α β * xiMat X 0 ∧ X.det = 1 ∧
      X * X * X = 1 := by
  obtain ⟨α, β, M, hNM, -⟩ :=
    exists_xi_decomp h2 h3 one_ne_zero hN (by rw [one_smul]; exact hsp)
  have hcube : N * N * N = rSc α β * rSc α β * rSc α β * xiMat (M * M * M) 0 := by
    rw [hNM, ← xiMat_mul_xiMat_zero h3, ← xiMat_mul_xiMat_zero h3]
    have c := rSc_comm h3 α β M 0
    calc rSc α β * xiMat M 0 * (rSc α β * xiMat M 0) * (rSc α β * xiMat M 0) =
        rSc α β * (xiMat M 0 * rSc α β) * (xiMat M 0 * rSc α β) * xiMat M 0 := by
          simp only [Matrix.mul_assoc]
      _ = rSc α β * (rSc α β * xiMat M 0) * (rSc α β * xiMat M 0) * xiMat M 0 := by rw [c]
      _ = rSc α β * rSc α β * (xiMat M 0 * rSc α β) * xiMat M 0 * xiMat M 0 := by
          simp only [Matrix.mul_assoc]
      _ = rSc α β * rSc α β * (rSc α β * xiMat M 0) * xiMat M 0 * xiMat M 0 := by rw [c]
      _ = rSc α β * rSc α β * rSc α β * (xiMat M 0 * xiMat M 0 * xiMat M 0) := by
          simp only [Matrix.mul_assoc]
  obtain ⟨a, b, hab⟩ : ∃ a b : K, rSc α β * rSc α β * rSc α β = rSc a b :=
    ⟨_, _, by rw [rSc_mul h3, rSc_mul h3]⟩
  rw [hab, rSc_mul_xiMat h3, hN3, ← xiMat_one] at hcube
  obtain ⟨hM3, -⟩ := xiMat_injective h3 hcube.symm
  have ha : a ≠ 0 := by
    intro h0
    rw [h0, zero_smul] at hM3
    have := congrFun (congrFun hM3 0) 0
    simp at this
  have hM3' : M * M * M = a⁻¹ • (1 : Matrix (Fin 2) (Fin 2) K) := by
    rw [← hM3, smul_smul, inv_mul_cancel₀ ha, one_smul]
  set δ := M.det with hδ
  have hδ3 : δ * δ * δ * (a * a) = 1 := by
    have e := congrArg Matrix.det hM3'
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_smul, Matrix.det_one, Fintype.card_fin,
      ← hδ] at e
    rw [e]
    field_simp
  have hδ0 : δ ≠ 0 := by
    intro h0
    rw [h0] at hδ3
    simp at hδ3
  refine ⟨α * (δ * a)⁻¹, β * (δ * a)⁻¹, (δ * a) • M, ?_, ?_, ?_⟩
  · rw [hNM, rSc_mul_xiMat h3, rSc_mul_xiMat h3, smul_smul, smul_smul, mul_assoc,
      inv_mul_cancel₀ (mul_ne_zero hδ0 ha), mul_one, mul_assoc, inv_mul_cancel₀
        (mul_ne_zero hδ0 ha), mul_one]
  · rw [Matrix.det_smul, Fintype.card_fin, ← hδ]
    linear_combination hδ3
  · rw [smul_mul_smul_comm, smul_mul_smul_comm, hM3', smul_smul]
    have e : δ * a * (δ * a) * (δ * a) * a⁻¹ = δ * δ * δ * (a * a) := by
      field_simp
    rw [e, hδ3, one_smul]

end Item211Lie3Proof

end CFSG.RankThree.PartTwo.Sec21
