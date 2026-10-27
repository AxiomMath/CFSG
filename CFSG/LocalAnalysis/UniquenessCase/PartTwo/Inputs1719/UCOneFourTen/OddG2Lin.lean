module

public import CFSG.RankThree.PartTwo.Sec21.Item223RankResProofCross
import CFSG.RankThree.PartTwo.Sec6.Item611Res3ProofG2
import CFSG.Foundations
import CFSG.GroupTheory.BaerSuzuki
import CFSG.RankThree.Asc83Table.Automizer
import CFSG.RankThree.PartTwo.NotationBlocks
import CFSG.RankThree.PartTwo.Sec21.Item21Statements
import CFSG.RankThree.PartTwo.Sec6.Item611ResProof
import CFSG.RankThree.PartTwo.Sec7.ThreeTranspositions

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UC410

open CFSG.RankThree.PartTwo.Sec21.Item223RankResProof CFSG.RankThree.PartOne.SEITZ11 Matrix
open CFSG.RankThree.PartTwo.Sec6.Res611G2Cent

variable {K : Type*} [Field K]

private theorem finrank_eigP_eq_three {M : Matrix (Fin 7) (Fin 7) K}
    (h2 : (2 : K) ≠ 0) (hM : M * M = 1)
    (hMB : M.transpose * G2Seven.gram K * M = G2Seven.gram K)
    (hMX : ∀ u v, M *ᵥ cross7 u v = cross7 (M *ᵥ u) (M *ᵥ v)) (hM1 : M ≠ 1) :
    Module.finrank K (eigP M) = 3 := by
  have hsum : Module.finrank K (eigP M) + Module.finrank K (eigM M) = 7 := by
    have h := finrank_split h2 hM ⊤ (fun _ _ => Submodule.mem_top)
    rw [finrank_top, Module.finrank_fin_fun, top_inf_eq, top_inf_eq] at h
    omega
  have := finrank_eigM_eq_four h2 hM hMB hMX hM1
  omega

private theorem transpose_mul_gram {A B : Matrix (Fin 7) (Fin 7) K}
    (hA : A.transpose * G2Seven.gram K * A = G2Seven.gram K)
    (hB : B.transpose * G2Seven.gram K * B = G2Seven.gram K) :
    (A * B).transpose * G2Seven.gram K * (A * B) = G2Seven.gram K := by
  rw [Matrix.transpose_mul]
  calc B.transpose * A.transpose * G2Seven.gram K * (A * B)
      = B.transpose * (A.transpose * G2Seven.gram K * A) * B := by simp only [mul_assoc]
    _ = G2Seven.gram K := by rw [hA, hB]

private theorem mulVec_cross_mul {A B : Matrix (Fin 7) (Fin 7) K}
    (hA : ∀ u v, A *ᵥ cross7 u v = cross7 (A *ᵥ u) (A *ᵥ v))
    (hB : ∀ u v, B *ᵥ cross7 u v = cross7 (B *ᵥ u) (B *ᵥ v)) :
    ∀ u v, (A * B) *ᵥ cross7 u v = cross7 ((A * B) *ᵥ u) ((A * B) *ᵥ v) := by
  intro u v
  rw [← Matrix.mulVec_mulVec, hB, hA, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]

private theorem mul_self_mul {A B : Matrix (Fin 7) (Fin 7) K}
    (hA : A * A = 1) (hB : B * B = 1) (hc : A * B = B * A) : (A * B) * (A * B) = 1 := by
  calc (A * B) * (A * B) = A * (B * A) * B := by simp only [mul_assoc]
    _ = A * (A * B) * B := by rw [hc]
    _ = (A * A) * (B * B) := by simp only [mul_assoc]
    _ = 1 := by rw [hA, hB, one_mul]

private theorem finrank_inf_eigP_eq_one {A B : Matrix (Fin 7) (Fin 7) K}
    (h2 : (2 : K) ≠ 0) (hA : A * A = 1) (hB : B * B = 1) (hc : A * B = B * A)
    (hBA : A.transpose * G2Seven.gram K * A = G2Seven.gram K)
    (hBB : B.transpose * G2Seven.gram K * B = G2Seven.gram K)
    (hXA : ∀ u v, A *ᵥ cross7 u v = cross7 (A *ᵥ u) (A *ᵥ v))
    (hXB : ∀ u v, B *ᵥ cross7 u v = cross7 (B *ᵥ u) (B *ᵥ v))
    (hA1 : A ≠ 1) (hB1 : B ≠ 1) (hAB1 : A * B ≠ 1) :
    Module.finrank K ↥(eigP A ⊓ eigP B) = 1 := by
  have hAB : (A * B) * (A * B) = 1 := mul_self_mul hA hB hc
  have hBAB : (A * B).transpose * G2Seven.gram K * (A * B) = G2Seven.gram K :=
    transpose_mul_gram hBA hBB
  have hXAB := mulVec_cross_mul hXA hXB
  have dA : Module.finrank K (eigP A) = 3 := finrank_eigP_eq_three h2 hA hBA hXA hA1
  have dB : Module.finrank K (eigP B) = 3 := finrank_eigP_eq_three h2 hB hBB hXB hB1
  have dAB : Module.finrank K (eigM (A * B)) = 4 :=
    finrank_eigM_eq_four h2 hAB hBAB hXAB hAB1
  have hcA : A * (A * B) = (A * B) * A := by
    rw [← mul_assoc, hA, one_mul, mul_assoc, ← hc, ← mul_assoc, hA, one_mul]
  have s₁ := finrank_split h2 hB (eigP A) fun v hv => mulVec_mem_eigP_of_commute hc hv
  have s₂ := finrank_split h2 hA (eigP B) fun v hv => mulVec_mem_eigP_of_commute hc.symm hv
  have s₃ := finrank_split h2 hA (eigM (A * B)) fun v hv =>
    mulVec_mem_eigM_of_commute hcA.symm hv
  have e₁ : eigM (A * B) ⊓ eigP A = eigP A ⊓ eigM B := by
    ext v
    simp only [Submodule.mem_inf, mem_eigP, mem_eigM]
    constructor
    · rintro ⟨h, h'⟩
      refine ⟨h', ?_⟩
      calc B *ᵥ v = (A * A * B) *ᵥ v := by rw [hA, one_mul]
        _ = A *ᵥ ((A * B) *ᵥ v) := by rw [Matrix.mulVec_mulVec, mul_assoc]
        _ = -v := by rw [h, Matrix.mulVec_neg, h']
    · rintro ⟨h, h'⟩
      exact ⟨by rw [← Matrix.mulVec_mulVec, h', Matrix.mulVec_neg, h], h⟩
  have e₂ : eigM (A * B) ⊓ eigM A = eigM A ⊓ eigP B := by
    ext v
    simp only [Submodule.mem_inf, mem_eigP, mem_eigM]
    constructor
    · rintro ⟨h, h'⟩
      refine ⟨h', ?_⟩
      calc B *ᵥ v = (A * A * B) *ᵥ v := by rw [hA, one_mul]
        _ = A *ᵥ ((A * B) *ᵥ v) := by rw [Matrix.mulVec_mulVec, mul_assoc]
        _ = v := by rw [h, Matrix.mulVec_neg, h', neg_neg]
    · rintro ⟨h, h'⟩
      exact ⟨by rw [← Matrix.mulVec_mulVec, h', h], h⟩
  rw [inf_comm (eigP B) (eigP A), inf_comm (eigP B) (eigM A)] at s₂
  rw [e₁, e₂] at s₃
  rw [dA] at s₁
  rw [dB] at s₂
  rw [dAB] at s₃
  omega

private theorem mulVec_comm_on_line {S : Submodule K (Fin 7 → K)}
    (hS : Module.finrank K S = 1) {A B : Matrix (Fin 7) (Fin 7) K}
    (hA : ∀ v ∈ S, A *ᵥ v ∈ S) (hB : ∀ v ∈ S, B *ᵥ v ∈ S) :
    ∀ v ∈ S, (A * B) *ᵥ v = (B * A) *ᵥ v := by
  intro v hv
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  by_cases hv0 : v = 0
  · subst hv0; simp
  · have hspan : S = K ∙ v := eq_span_singleton_of_mem_of_finrank_eq_one hS hv hv0
    obtain ⟨c', hc'⟩ := Submodule.mem_span_singleton.mp (hspan ▸ hB v hv)
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp (hspan ▸ hA v hv)
    have h1 : A *ᵥ (B *ᵥ v) = (c' * c) • v := by
      rw [← hc', Matrix.mulVec_smul, ← hc, smul_smul]
    have h2 : B *ᵥ (A *ᵥ v) = (c * c') • v := by
      rw [← hc, Matrix.mulVec_smul, ← hc', smul_smul]
    rw [h1, h2, mul_comm]

private theorem le_of_pair {T : Submodule K (Fin 7 → K)} {N N' : Matrix (Fin 7) (Fin 7) K}
    (hmem : ∀ v : Fin 7 → K, v ∈ T ↔ (N * N') *ᵥ v = (N' * N) *ᵥ v)
    (h2 : (2 : K) ≠ 0) {A B : Matrix (Fin 7) (Fin 7) K}
    (hA : A * A = 1) (hB : B * B = 1) (hc : A * B = B * A)
    (hBA : A.transpose * G2Seven.gram K * A = G2Seven.gram K)
    (hBB : B.transpose * G2Seven.gram K * B = G2Seven.gram K)
    (hXA : ∀ u v, A *ᵥ cross7 u v = cross7 (A *ᵥ u) (A *ᵥ v))
    (hXB : ∀ u v, B *ᵥ cross7 u v = cross7 (B *ᵥ u) (B *ᵥ v))
    (hA1 : A ≠ 1) (hB1 : B ≠ 1) (hAB1 : A * B ≠ 1)
    (hNA : N * A = A * N) (hNB : N * B = B * N)
    (hN'A : N' * A = A * N') (hN'B : N' * B = B * N') :
    eigP A ⊓ eigP B ≤ T := by
  intro v hv
  rw [hmem v]
  refine mulVec_comm_on_line
    (finrank_inf_eigP_eq_one h2 hA hB hc hBA hBB hXA hXB hA1 hB1 hAB1) ?_ ?_ v hv
  · intro w hw
    exact ⟨mulVec_mem_eigP_of_commute hNA.symm hw.1,
      mulVec_mem_eigP_of_commute hNB.symm hw.2⟩
  · intro w hw
    exact ⟨mulVec_mem_eigP_of_commute hN'A.symm hw.1,
      mulVec_mem_eigP_of_commute hN'B.symm hw.2⟩

private theorem inf_eigM_eigM_le_eigP_mul {A B : Matrix (Fin 7) (Fin 7) K} :
    eigM A ⊓ eigM B ≤ eigP (A * B) := by
  intro v hv
  rw [mem_eigP, ← Matrix.mulVec_mulVec, mem_eigM.mp hv.2, Matrix.mulVec_neg,
    mem_eigM.mp hv.1, neg_neg]

private theorem le_of_le_eig {T S : Submodule K (Fin 7 → K)} (h2 : (2 : K) ≠ 0)
    {M : Matrix (Fin 7) (Fin 7) K} (hM : M * M = 1) (hMS : ∀ v ∈ S, M *ᵥ v ∈ S)
    (hP : S ⊓ eigP M ≤ T) (hQ : S ⊓ eigM M ≤ T) : S ≤ T := by
  intro v hv
  rw [half_decomp (M := M) h2 v]
  refine T.add_mem (hP ?_) (hQ ?_)
  · exact ⟨S.smul_mem _ (S.add_mem hv (hMS v hv)), half_add_mem_eigP hM v⟩
  · exact ⟨S.smul_mem _ (S.sub_mem hv (hMS v hv)), half_sub_mem_eigM hM v⟩

theorem commute_of_commute_three_involutions {K : Type*} [Field K] (h2 : (2 : K) ≠ 0)
    {M₁ M₂ M₃ : Matrix (Fin 7) (Fin 7) K}
    (hM₁ : M₁ * M₁ = 1) (hM₂ : M₂ * M₂ = 1) (hM₃ : M₃ * M₃ = 1)
    (h12 : M₁ * M₂ = M₂ * M₁) (h13 : M₁ * M₃ = M₃ * M₁) (h23 : M₂ * M₃ = M₃ * M₂)
    (hB₁ : M₁.transpose * G2Seven.gram K * M₁ = G2Seven.gram K)
    (hB₂ : M₂.transpose * G2Seven.gram K * M₂ = G2Seven.gram K)
    (hB₃ : M₃.transpose * G2Seven.gram K * M₃ = G2Seven.gram K)
    (hX₁ : ∀ u v, M₁ *ᵥ cross7 u v = cross7 (M₁ *ᵥ u) (M₁ *ᵥ v))
    (hX₂ : ∀ u v, M₂ *ᵥ cross7 u v = cross7 (M₂ *ᵥ u) (M₂ *ᵥ v))
    (hX₃ : ∀ u v, M₃ *ᵥ cross7 u v = cross7 (M₃ *ᵥ u) (M₃ *ᵥ v))
    (hne₁ : M₁ ≠ 1) (hne₂ : M₂ ≠ 1) (hne₃ : M₃ ≠ 1) (hne₁₂ : M₁ * M₂ ≠ 1)
    (hne₁₃ : M₁ * M₃ ≠ 1) (hne₂₃ : M₂ * M₃ ≠ 1) (hne₁₂₃ : M₁ * M₂ * M₃ ≠ 1)
    {N N' : Matrix (Fin 7) (Fin 7) K}
    (hN₁ : N * M₁ = M₁ * N) (hN₂ : N * M₂ = M₂ * N) (hN₃ : N * M₃ = M₃ * N)
    (hN'₁ : N' * M₁ = M₁ * N') (hN'₂ : N' * M₂ = M₂ * N') (hN'₃ : N' * M₃ = M₃ * N') :
    N * N' = N' * N := by
  have hM₁₂ : (M₁ * M₂) * (M₁ * M₂) = 1 := mul_self_mul hM₁ hM₂ h12
  have hM₁₃ : (M₁ * M₃) * (M₁ * M₃) = 1 := mul_self_mul hM₁ hM₃ h13
  have hM₂₃ : (M₂ * M₃) * (M₂ * M₃) = 1 := mul_self_mul hM₂ hM₃ h23
  have hB₁₂ : (M₁ * M₂).transpose * G2Seven.gram K * (M₁ * M₂) = G2Seven.gram K :=
    transpose_mul_gram hB₁ hB₂
  have hB₁₃ : (M₁ * M₃).transpose * G2Seven.gram K * (M₁ * M₃) = G2Seven.gram K :=
    transpose_mul_gram hB₁ hB₃
  have hB₂₃ : (M₂ * M₃).transpose * G2Seven.gram K * (M₂ * M₃) = G2Seven.gram K :=
    transpose_mul_gram hB₂ hB₃
  have hX₁₂ := mulVec_cross_mul hX₁ hX₂
  have hX₁₃ := mulVec_cross_mul hX₁ hX₃
  have hX₂₃ := mulVec_cross_mul hX₂ hX₃
  have hc₃₁₂ : Commute M₃ (M₁ * M₂) := Commute.mul_right h13.symm h23.symm
  have hc₂₁₃ : Commute M₂ (M₁ * M₃) := Commute.mul_right h12.symm h23
  have hc₁₂₃ : Commute M₁ (M₂ * M₃) := Commute.mul_right h12 h13
  have hc₁₂₁₃ : Commute (M₁ * M₂) (M₁ * M₃) :=
    (Commute.mul_left (Commute.refl M₁) h12.symm).mul_right (Commute.mul_left h13 h23)
  have hne₃₁₂ : M₃ * (M₁ * M₂) ≠ 1 := by
    rw [show M₃ * (M₁ * M₂) = M₁ * M₂ * M₃ from by
      calc M₃ * (M₁ * M₂) = (M₃ * M₁) * M₂ := by rw [mul_assoc]
        _ = (M₁ * M₃) * M₂ := by rw [← h13]
        _ = M₁ * (M₃ * M₂) := by rw [mul_assoc]
        _ = M₁ * (M₂ * M₃) := by rw [h23]
        _ = M₁ * M₂ * M₃ := by rw [mul_assoc]]
    exact hne₁₂₃
  have hne₂₁₃ : M₂ * (M₁ * M₃) ≠ 1 := by
    rw [show M₂ * (M₁ * M₃) = M₁ * M₂ * M₃ from by
      calc M₂ * (M₁ * M₃) = (M₂ * M₁) * M₃ := by rw [mul_assoc]
        _ = (M₁ * M₂) * M₃ := by rw [h12]
        _ = M₁ * M₂ * M₃ := rfl]
    exact hne₁₂₃
  have hne₁₂₃' : M₁ * (M₂ * M₃) ≠ 1 := by
    rw [← mul_assoc]
    exact hne₁₂₃
  have hne₁₂₁₃ : (M₁ * M₂) * (M₁ * M₃) ≠ 1 := by
    rw [show (M₁ * M₂) * (M₁ * M₃) = M₂ * M₃ from by
      calc (M₁ * M₂) * (M₁ * M₃)
          = M₁ * (M₂ * (M₁ * M₃)) := by rw [mul_assoc]
        _ = M₁ * ((M₂ * M₁) * M₃) := by rw [mul_assoc]
        _ = M₁ * ((M₁ * M₂) * M₃) := by rw [← h12]
        _ = M₁ * (M₁ * (M₂ * M₃)) := by rw [mul_assoc]
        _ = (M₁ * M₁) * (M₂ * M₃) := by rw [← mul_assoc]
        _ = M₂ * M₃ := by rw [hM₁, one_mul]]
    exact hne₂₃
  have hcN₁₂ : Commute N (M₁ * M₂) := Commute.mul_right hN₁ hN₂
  have hcN₁₃ : Commute N (M₁ * M₃) := Commute.mul_right hN₁ hN₃
  have hcN₂₃ : Commute N (M₂ * M₃) := Commute.mul_right hN₂ hN₃
  have hcN'₁₂ : Commute N' (M₁ * M₂) := Commute.mul_right hN'₁ hN'₂
  have hcN'₁₃ : Commute N' (M₁ * M₃) := Commute.mul_right hN'₁ hN'₃
  have hcN'₂₃ : Commute N' (M₂ * M₃) := Commute.mul_right hN'₂ hN'₃
  set T : Submodule K (Fin 7 → K) := LinearMap.ker (N * N' - N' * N).mulVecLin with hT
  have hmem : ∀ v : Fin 7 → K, v ∈ T ↔ (N * N') *ᵥ v = (N' * N) *ᵥ v := by
    intro v
    rw [hT, LinearMap.mem_ker, Matrix.mulVecLin_apply, Matrix.sub_mulVec, sub_eq_zero]
  have hS₁₂ : eigP M₁ ⊓ eigP M₂ ≤ T :=
    le_of_pair hmem h2 hM₁ hM₂ h12 hB₁ hB₂ hX₁ hX₂ hne₁ hne₂ hne₁₂ hN₁ hN₂ hN'₁ hN'₂
  have hS₁₃ : eigP M₁ ⊓ eigP M₃ ≤ T :=
    le_of_pair hmem h2 hM₁ hM₃ h13 hB₁ hB₃ hX₁ hX₃ hne₁ hne₃ hne₁₃ hN₁ hN₃ hN'₁ hN'₃
  have hS₂₃ : eigP M₂ ⊓ eigP M₃ ≤ T :=
    le_of_pair hmem h2 hM₂ hM₃ h23 hB₂ hB₃ hX₂ hX₃ hne₂ hne₃ hne₂₃ hN₂ hN₃ hN'₂ hN'₃
  have hS₃₁₂ : eigP M₃ ⊓ eigP (M₁ * M₂) ≤ T :=
    le_of_pair hmem h2 hM₃ hM₁₂ hc₃₁₂.eq hB₃ hB₁₂ hX₃ hX₁₂ hne₃ hne₁₂ hne₃₁₂ hN₃ hcN₁₂.eq
      hN'₃ hcN'₁₂.eq
  have hS₂₁₃ : eigP M₂ ⊓ eigP (M₁ * M₃) ≤ T :=
    le_of_pair hmem h2 hM₂ hM₁₃ hc₂₁₃.eq hB₂ hB₁₃ hX₂ hX₁₃ hne₂ hne₁₃ hne₂₁₃ hN₂ hcN₁₃.eq
      hN'₂ hcN'₁₃.eq
  have hS₁₂₃ : eigP M₁ ⊓ eigP (M₂ * M₃) ≤ T :=
    le_of_pair hmem h2 hM₁ hM₂₃ hc₁₂₃.eq hB₁ hB₂₃ hX₁ hX₂₃ hne₁ hne₂₃ hne₁₂₃' hN₁ hcN₂₃.eq
      hN'₁ hcN'₂₃.eq
  have hS₁₂₁₃ : eigP (M₁ * M₂) ⊓ eigP (M₁ * M₃) ≤ T :=
    le_of_pair hmem h2 hM₁₂ hM₁₃ hc₁₂₁₃.eq hB₁₂ hB₁₃ hX₁₂ hX₁₃ hne₁₂ hne₁₃ hne₁₂₁₃ hcN₁₂.eq
      hcN₁₃.eq hcN'₁₂.eq hcN'₁₃.eq
  have hPM : eigP M₁ ⊓ eigM M₂ ≤ T :=
    le_of_le_eig h2 hM₃
      (fun v hv => ⟨mulVec_mem_eigP_of_commute h13 hv.1,
        mulVec_mem_eigM_of_commute h23 hv.2⟩)
      (le_trans (inf_le_inf inf_le_left le_rfl) hS₁₃)
      (le_trans (le_inf (le_trans inf_le_left inf_le_left)
        (le_trans (le_inf (le_trans inf_le_left inf_le_right) inf_le_right)
          inf_eigM_eigM_le_eigP_mul)) hS₁₂₃)
  have hMP : eigM M₁ ⊓ eigP M₂ ≤ T :=
    le_of_le_eig h2 hM₃
      (fun v hv => ⟨mulVec_mem_eigM_of_commute h13 hv.1,
        mulVec_mem_eigP_of_commute h23 hv.2⟩)
      (le_trans (inf_le_inf inf_le_right le_rfl) hS₂₃)
      (le_trans (le_inf (le_trans inf_le_left inf_le_right)
        (le_trans (le_inf (le_trans inf_le_left inf_le_left) inf_le_right)
          inf_eigM_eigM_le_eigP_mul)) hS₂₁₃)
  have hMM : eigM M₁ ⊓ eigM M₂ ≤ T :=
    le_of_le_eig h2 hM₃
      (fun v hv => ⟨mulVec_mem_eigM_of_commute h13 hv.1,
        mulVec_mem_eigM_of_commute h23 hv.2⟩)
      (le_trans (le_inf inf_le_right (le_trans inf_le_left inf_eigM_eigM_le_eigP_mul)) hS₃₁₂)
      (le_trans (le_inf (le_trans inf_le_left inf_eigM_eigM_le_eigP_mul)
        (le_trans (le_inf (le_trans inf_le_left inf_le_left) inf_le_right)
          inf_eigM_eigM_le_eigP_mul)) hS₁₂₁₃)
  have hP : eigP M₁ ≤ T :=
    le_of_le_eig h2 hM₂ (fun v hv => mulVec_mem_eigP_of_commute h12 hv) hS₁₂ hPM
  have hM : eigM M₁ ≤ T :=
    le_of_le_eig h2 hM₂ (fun v hv => mulVec_mem_eigM_of_commute h12 hv) hMP hMM
  have htop : (⊤ : Submodule K (Fin 7 → K)) ≤ T :=
    le_of_le_eig (S := ⊤) h2 hM₁ (fun _ _ => Submodule.mem_top)
      (by rwa [top_inf_eq]) (by rwa [top_inf_eq])
  refine Matrix.ext_iff_mulVec.mpr fun v => ?_
  exact (hmem v).mp (htop Submodule.mem_top)


end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UC410
