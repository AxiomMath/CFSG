module

public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSPosDefs

public section

namespace CFSG.StandardType.QTwo

open CFSG.StandardType CFSG.ClassicalInvolution.Phan CFSG.LieType.Universal.Unitary
  CFSG.LieType.BorelTits Matrix

private theorem qTwoFrontQ_invol_conjTr_smul {F : Type*} [Field F] (σ : F ≃+* F) {n : ℕ} (c : F)
    (M : Matrix (Fin n) (Fin n) F) : conjTr σ (c • M) = σ c • conjTr σ M := by
  ext i j
  simp [conjTr]

private theorem qTwoFrontQ_invol_not_scalar {K : Type} [Field K] {n : ℕ}
    {N : Matrix (Fin n) (Fin n) K} (hN2 : N * N = 0) (hN0 : N ≠ 0) {a : K} (ha : a ≠ 0)
    (c : K) : (1 : Matrix (Fin n) (Fin n) K) + a • N ≠ Matrix.diagonal (fun _ => c) := by
  intro h
  have hdiag : a • N = Matrix.diagonal (fun _ => c) - 1 := by
    rw [← h]
    abel
  have hdiag' : a • N = Matrix.diagonal (fun _ => c - 1) := by
    rw [hdiag, ← Matrix.diagonal_one, ← Matrix.diagonal_sub]
  have hsq : (Matrix.diagonal (fun _ => (c - 1) ^ 2) : Matrix (Fin n) (Fin n) K) = 0 := by
    have h2 := congrArg (fun M => M * M) hdiag'
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hN2, smul_zero,
      Matrix.diagonal_mul_diagonal] at h2
    rw [h2]
    congr 1
    ext i
    ring
  by_cases hn : n = 0
  · subst hn
    exact hN0 (by funext i j; exact Fin.elim0 i)
  · let i : Fin n := ⟨0, Nat.pos_of_ne_zero hn⟩
    have hii := congrArg (fun M : Matrix (Fin n) (Fin n) K => M i i) hsq
    simp only [Matrix.diagonal_apply_eq, Matrix.zero_apply] at hii
    have hc : c = 1 := by
      exact sub_eq_zero.mp ((pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0)).mp hii)
    rw [hc] at hdiag'
    have hzero : a • N = 0 := by simpa using hdiag'
    have hNzero : N = 0 := by
      have h3 := congrArg (fun M => a⁻¹ • M) hzero
      simpa [smul_smul, inv_mul_cancel₀ ha, one_smul] using h3
    exact hN0 hNzero

theorem qTwoFrontQ_second_involution {K : Type} [Field K] [Finite K] [CharP K 2] {f d : ℕ}
    (hK : Nat.card K = (2 ^ f) ^ 2) {ω : K} (hω : unitaryInvolution K 2 f ω = ω) (hω0 : ω ≠ 0)
    (hω1 : ω ≠ 1) {u : Su K 2 f d} (hu2 : u * u = 1) (hu1 : u ≠ 1) :
    ∃ v : Su K 2 f d, v * v = 1 ∧ u * v = v * u ∧
      (∀ g : Matrix (Fin d) (Fin d) K,
        g * ((u : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) =
          ((u : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) * g →
        g * ((v : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) =
          ((v : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) * g) ∧
      (∀ c : K, ((v : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) ≠ Matrix.diagonal (fun _ => c)) ∧
      (∀ c : K, (((u * v : Su K 2 f d) : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) ≠
        Matrix.diagonal (fun _ => c)) := by
  let σ : K ≃+* K := unitaryInvolution K 2 f
  let U : Matrix (Fin d) (Fin d) K := ((u : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)
  let N : Matrix (Fin d) (Fin d) K := U - 1
  let V : Matrix (Fin d) (Fin d) K := 1 + ω • N
  have hNdef : N = U - 1 := rfl
  have hVdef : V = 1 + ω • N := rfl
  have huval : ((u : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = U := rfl
  have hU2 : U * U = 1 := by
    have h := congrArg (fun x : Su K 2 f d => (((x : GL (Fin d) K)) :
      Matrix (Fin d) (Fin d) K)) hu2
    simpa [U] using h
  have hN2 : N * N = 0 := by
    have hUU : U + U = 0 := by
      rw [← two_smul K U, CharTwo.two_eq_zero, zero_smul]
    have h11 : (1 : Matrix (Fin d) (Fin d) K) + 1 = 0 := by
      rw [← two_smul K (1 : Matrix (Fin d) (Fin d) K), CharTwo.two_eq_zero, zero_smul]
    have hneg1 : -(1 : Matrix (Fin d) (Fin d) K) = 1 := by
      rw [neg_eq_iff_add_eq_zero]
      exact h11
    have hNadd : N = U + 1 := by rw [hNdef, sub_eq_add_neg, hneg1]
    simp only [hNadd]
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.mul_one, Matrix.one_mul, hU2]
    rw [show (1 + U) + (U + 1) = (1 + 1) + (U + U) by abel, hUU, h11, add_zero]
  have hUconj : conjTr σ U * U = 1 := (mem_SUid.mp u.2).2
  have hconjU : conjTr σ U = U := by
    calc conjTr σ U = conjTr σ U * (U * U) := by rw [hU2, Matrix.mul_one]
      _ = (conjTr σ U * U) * U := by rw [Matrix.mul_assoc]
      _ = U := by rw [hUconj, Matrix.one_mul]
  have hconjN : conjTr σ N = N := by
    simp only [hNdef]
    rw [conjTr_sub, conjTr_one, hconjU]
  have hV2 : V * V = 1 := by
    have hωω : ω • N + ω • N = 0 := by
      rw [← two_smul K (ω • N), CharTwo.two_eq_zero, zero_smul]
    simp only [hVdef, Matrix.mul_add, Matrix.add_mul, Matrix.one_mul, Matrix.mul_one,
      Matrix.mul_smul, Matrix.smul_mul, smul_smul, hN2, smul_zero, add_zero]
    rw [add_assoc, hωω, add_zero]
  have hconjV : conjTr σ V = V := by
    have hσω : σ ω = ω := hω
    simp only [hVdef]
    rw [conjTr_add, conjTr_one, qTwoFrontQ_invol_conjTr_smul σ ω N, hconjN, hσω]
  have hunit : conjTr σ V * V = 1 := by rw [hconjV, hV2]
  have hVdet : V.det = 1 := by
    have hnil : IsNilpotent (ω • N) := ⟨2, by
      rw [pow_two, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hN2, smul_zero]⟩
    have h := det_one_add_of_isNilpotent (F := K) 2 hnil
    simpa [hVdef] using h
  have hN0 : N ≠ 0 := by
    intro hN
    apply hu1
    have hU1 : U = 1 := sub_eq_zero.mp (by simpa [hNdef] using hN)
    apply Subtype.ext
    apply Units.ext
    simpa [U] using hU1
  let Vgl : GL (Fin d) K := ⟨V, V, hV2, hV2⟩
  have hVgl : (Vgl : Matrix (Fin d) (Fin d) K) = V := rfl
  let v : Su K 2 f d := ⟨Vgl, by rw [hVgl]; exact hVdet, by rw [hVgl]; exact hunit⟩
  have hvval : ((v : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = V := rfl
  have hUN : U * N = N * U := by
    simp only [hNdef, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul, hU2]
  have hUV : U * V = V * U := by
    simp only [hVdef, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul,
      Matrix.mul_smul, Matrix.smul_mul, hUN]
  have hcomm : ∀ g : Matrix (Fin d) (Fin d) K, g * U = U * g → g * V = V * g := by
    intro g hg
    have hgN : g * N = N * g := by
      simp only [hNdef, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul, hg]
    simp only [hVdef, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul,
      Matrix.mul_smul, Matrix.smul_mul]
    rw [hgN]
  have hvv : v * v = 1 := by
    apply Subtype.ext
    apply Units.ext
    rw [Subgroup.coe_mul, Units.val_mul, Subgroup.coe_one, Units.val_one, hvval, hV2]
  have huv : u * v = v * u := by
    apply Subtype.ext
    apply Units.ext
    rw [Subgroup.coe_mul, Units.val_mul, Subgroup.coe_mul, Units.val_mul, huval, hvval, hUV]
  have hUVeq : U * V = 1 + (1 + ω) • N := by
    have hUeq : U = N + 1 := by rw [hNdef, sub_add_cancel]
    simp only [hUeq, hVdef, Matrix.add_mul, Matrix.one_mul, Matrix.mul_add, Matrix.mul_one,
      Matrix.mul_smul, smul_smul, hN2, smul_zero, add_zero, add_smul, one_smul]
    abel
  refine ⟨v, hvv, huv, ?_, ?_, ?_⟩
  · intro g hg
    have hgU : g * U = U * g := by rwa [huval] at hg
    have h := hcomm g hgU
    rwa [← hvval] at h
  · intro c
    rw [hvval]
    exact qTwoFrontQ_invol_not_scalar hN2 hN0 hω0 c
  · intro c
    have huvval : (((u * v : Su K 2 f d) : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) =
        1 + (1 + ω) • N := by
      rw [Subgroup.coe_mul, Units.val_mul, huval, hvval, hUVeq]
    rw [huvval]
    have h1ω : (1 + ω : K) ≠ 0 := by
      intro h
      exact hω1 (CharTwo.add_eq_zero.mp h).symm
    exact qTwoFrontQ_invol_not_scalar hN2 hN0 h1ω c

end CFSG.StandardType.QTwo

end
