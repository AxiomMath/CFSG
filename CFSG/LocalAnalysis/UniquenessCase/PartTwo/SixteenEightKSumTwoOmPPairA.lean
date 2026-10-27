module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.OrthModel

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open
open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
open Matrix

variable {K : Type} [Field K] {m : ℕ}

theorem s16k_single_inl_dot (i : Fin m) (v : Fin m ⊕ Fin m → K) :
    (Pi.single (Sum.inl i) 1 : Fin m ⊕ Fin m → K) ⬝ᵥ (plusM m K *ᵥ v) = v (Sum.inr i) := by
  rw [single_dot_plusM]; rfl

theorem s16k_single_inr_dot (i : Fin m) (v : Fin m ⊕ Fin m → K) :
    (Pi.single (Sum.inr i) 1 : Fin m ⊕ Fin m → K) ⬝ᵥ (plusM m K *ᵥ v) = v (Sum.inl i) := by
  rw [single_dot_plusM]; rfl

theorem s16k_Q_add_smul {ι K : Type} [Fintype ι] [Field K]
    {Q : (ι → K) → K} {M : Matrix ι ι K} (h : IsQuadWith Q M) {a w : ι → K}
    (hQw : Q w = 0) (haw : a ⬝ᵥ (M *ᵥ w) = 0) (μ : K) :
    Q (a + μ • w) = Q a := by
  rw [h.add, h.smul, hQw, Matrix.mulVec_smul, dotProduct_smul, haw, smul_eq_mul]
  ring

theorem s16k_dot_add_smul {ι K : Type} [Fintype ι] [Field K]
    {M : Matrix ι ι K} {a b w : ι → K} (hww : w ⬝ᵥ (M *ᵥ w) = 0) (μ μ' : K) :
    (a + μ • w) ⬝ᵥ (M *ᵥ (b + μ' • w)) =
      a ⬝ᵥ (M *ᵥ b) + μ' * (a ⬝ᵥ (M *ᵥ w)) + μ * (w ⬝ᵥ (M *ᵥ b)) := by
  simp only [Matrix.mulVec_add, Matrix.mulVec_smul, dotProduct_add, add_dotProduct,
    dotProduct_smul, smul_dotProduct, smul_eq_mul, hww]
  ring

theorem s16k_dot_add_smul_eq {ι K : Type} [Fintype ι] [Field K]
    {M : Matrix ι ι K} {a b w : ι → K} (hww : w ⬝ᵥ (M *ᵥ w) = 0)
    (haw : a ⬝ᵥ (M *ᵥ w) = 0) (hwb : w ⬝ᵥ (M *ᵥ b) = 0) (μ μ' : K) :
    (a + μ • w) ⬝ᵥ (M *ᵥ (b + μ' • w)) = a ⬝ᵥ (M *ᵥ b) := by
  rw [s16k_dot_add_smul hww, haw, hwb, mul_zero, mul_zero, add_zero, add_zero]

theorem s16k_v_add_smul {ι K : Type} [Fintype ι] [Field K] [CharP K 2]
    {M : Matrix ι ι K} {a w v : ι → K} (hvw : v ⬝ᵥ (M *ᵥ w) ≠ 0) :
    v ⬝ᵥ (M *ᵥ (a + (v ⬝ᵥ (M *ᵥ a) / (v ⬝ᵥ (M *ᵥ w))) • w)) = 0 := by
  have hμ : (v ⬝ᵥ (M *ᵥ a) / (v ⬝ᵥ (M *ᵥ w))) * (v ⬝ᵥ (M *ᵥ w)) = v ⬝ᵥ (M *ᵥ a) :=
    div_mul_cancel₀ _ hvw
  simp only [Matrix.mulVec_add, Matrix.mulVec_smul, dotProduct_add, dotProduct_smul,
    smul_eq_mul]
  linear_combination (v ⬝ᵥ (M *ᵥ a)) * two_eq_zero_K (K := K) + hμ

theorem s16k_pairs_of_singular_explicit {ι K : Type} [Fintype ι] [Field K] [CharP K 2]
    {Q : (ι → K) → K} {M : Matrix ι ι K} (h : IsQuadWith Q M)
    {a₁ a₁' a₂ a₂' wc v : ι → K}
    (h1 : Q a₁ = 1) (h1' : Q a₁' = 1) (h11 : a₁ ⬝ᵥ (M *ᵥ a₁') = 1)
    (h2 : Q a₂ = 1) (h2' : Q a₂' = 1) (h22 : a₂ ⬝ᵥ (M *ᵥ a₂') = 1)
    (h12 : a₁ ⬝ᵥ (M *ᵥ a₂) = 0) (h12' : a₁ ⬝ᵥ (M *ᵥ a₂') = 0)
    (h1'2 : a₁' ⬝ᵥ (M *ᵥ a₂) = 0) (h1'2' : a₁' ⬝ᵥ (M *ᵥ a₂') = 0)
    (hwcQ : Q wc = 0) (hwc1 : wc ⬝ᵥ (M *ᵥ a₁) = 0) (hwc1' : wc ⬝ᵥ (M *ᵥ a₁') = 0)
    (hwc2 : wc ⬝ᵥ (M *ᵥ a₂) = 0) (hwc2' : wc ⬝ᵥ (M *ᵥ a₂') = 0)
    (hvwc : v ⬝ᵥ (M *ᵥ wc) ≠ 0) :
    ∃ b₁ b₁' b₂ b₂' : ι → K,
      b₁ = a₁ + (v ⬝ᵥ (M *ᵥ a₁) / (v ⬝ᵥ (M *ᵥ wc))) • wc ∧
      b₁' = a₁' + (v ⬝ᵥ (M *ᵥ a₁') / (v ⬝ᵥ (M *ᵥ wc))) • wc ∧
      b₂ = a₂ + (v ⬝ᵥ (M *ᵥ a₂) / (v ⬝ᵥ (M *ᵥ wc))) • wc ∧
      b₂' = a₂' + (v ⬝ᵥ (M *ᵥ a₂') / (v ⬝ᵥ (M *ᵥ wc))) • wc ∧
      Q b₁ = 1 ∧ Q b₁' = 1 ∧ b₁ ⬝ᵥ (M *ᵥ b₁') = 1 ∧
      Q b₂ = 1 ∧ Q b₂' = 1 ∧ b₂ ⬝ᵥ (M *ᵥ b₂') = 1 ∧
      b₁ ⬝ᵥ (M *ᵥ b₂) = 0 ∧ b₁ ⬝ᵥ (M *ᵥ b₂') = 0 ∧
      b₁' ⬝ᵥ (M *ᵥ b₂) = 0 ∧ b₁' ⬝ᵥ (M *ᵥ b₂') = 0 ∧
      v ⬝ᵥ (M *ᵥ b₁) = 0 ∧ v ⬝ᵥ (M *ᵥ b₁') = 0 ∧
      v ⬝ᵥ (M *ᵥ b₂) = 0 ∧ v ⬝ᵥ (M *ᵥ b₂') = 0 := by
  have hww : wc ⬝ᵥ (M *ᵥ wc) = 0 := h.self wc
  have hw1 : a₁ ⬝ᵥ (M *ᵥ wc) = 0 := (h.symm a₁ wc).trans hwc1
  have hw1' : a₁' ⬝ᵥ (M *ᵥ wc) = 0 := (h.symm a₁' wc).trans hwc1'
  have hw2 : a₂ ⬝ᵥ (M *ᵥ wc) = 0 := (h.symm a₂ wc).trans hwc2
  have hw2' : a₂' ⬝ᵥ (M *ᵥ wc) = 0 := (h.symm a₂' wc).trans hwc2'
  refine ⟨a₁ + (v ⬝ᵥ (M *ᵥ a₁) / (v ⬝ᵥ (M *ᵥ wc))) • wc,
    a₁' + (v ⬝ᵥ (M *ᵥ a₁') / (v ⬝ᵥ (M *ᵥ wc))) • wc,
    a₂ + (v ⬝ᵥ (M *ᵥ a₂) / (v ⬝ᵥ (M *ᵥ wc))) • wc,
    a₂' + (v ⬝ᵥ (M *ᵥ a₂') / (v ⬝ᵥ (M *ᵥ wc))) • wc,
    rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [s16k_Q_add_smul h hwcQ hw1, h1]
  · rw [s16k_Q_add_smul h hwcQ hw1', h1']
  · rw [s16k_dot_add_smul_eq hww hw1 hwc1', h11]
  · rw [s16k_Q_add_smul h hwcQ hw2, h2]
  · rw [s16k_Q_add_smul h hwcQ hw2', h2']
  · rw [s16k_dot_add_smul_eq hww hw2 hwc2', h22]
  · rw [s16k_dot_add_smul_eq hww hw1 hwc2, h12]
  · rw [s16k_dot_add_smul_eq hww hw1 hwc2', h12']
  · rw [s16k_dot_add_smul_eq hww hw1' hwc2, h1'2]
  · rw [s16k_dot_add_smul_eq hww hw1' hwc2', h1'2']
  · exact s16k_v_add_smul hvwc
  · exact s16k_v_add_smul hvwc
  · exact s16k_v_add_smul hvwc
  · exact s16k_v_add_smul hvwc

theorem s16k_exists_two_ne {m : ℕ} (hm : 4 ≤ m) (c₁ c₂ : Fin m) :
    ∃ i j : Fin m, i ≠ j ∧ i ≠ c₁ ∧ i ≠ c₂ ∧ j ≠ c₁ ∧ j ≠ c₂ := by
  have hcard : 1 < ((Finset.univ.erase c₁).erase c₂).card := by
    rw [Finset.card_erase_eq_ite, Finset.card_erase_eq_ite, Finset.card_univ,
      Fintype.card_fin]
    split_ifs <;> omega
  obtain ⟨i, hi, j, hj, hij⟩ := Finset.one_lt_card.mp hcard
  have hi2 : i ≠ c₂ ∧ i ∈ Finset.univ.erase c₁ := Finset.mem_erase.mp hi
  have hj2 : j ≠ c₂ ∧ j ∈ Finset.univ.erase c₁ := Finset.mem_erase.mp hj
  exact ⟨i, j, hij, (Finset.mem_erase.mp hi2.2).1, hi2.1,
    (Finset.mem_erase.mp hj2.2).1, hj2.1⟩

def s16k_plusD (i j : Fin m) : Fin m ⊕ Fin m → K :=
  Pi.single (Sum.inl i) 1 + Pi.single (Sum.inr i) 1 + Pi.single (Sum.inl j) 1

theorem s16k_Q_plusD {i j : Fin m} (hij : i ≠ j) :
    StatedQuadPlus m K (s16k_plusD (K := K) i j) = 1 := by
  simp [CFSG.Open.StatedQuadPlus, s16k_plusD, Pi.single_apply, hij, hij.symm]

theorem s16k_B_plusD {i j : Fin m} (hij : i ≠ j) :
    plusA j ⬝ᵥ (plusM m K *ᵥ s16k_plusD (K := K) i j) = 1 := by
  unfold plusA
  rw [add_dotProduct, s16k_single_inl_dot, s16k_single_inr_dot]
  simp [s16k_plusD, Pi.single_apply, hij, hij.symm]

theorem s16k_dot_plusA_plusA [CharP K 2] {i j : Fin m} (hij : i ≠ j) :
    plusA i ⬝ᵥ (plusM m K *ᵥ plusA j) = 0 := by
  unfold plusA
  rw [add_dotProduct, s16k_single_inl_dot, s16k_single_inr_dot]
  simp [plusA, Pi.single_apply, hij, hij.symm]
  try linear_combination two_eq_zero_K (K := K)

theorem s16k_dot_plusA_plusD [CharP K 2] {i j : Fin m} (hij : i ≠ j) :
    plusA i ⬝ᵥ (plusM m K *ᵥ s16k_plusD (K := K) i j) = 0 := by
  unfold plusA
  rw [add_dotProduct, s16k_single_inl_dot, s16k_single_inr_dot]
  simp [s16k_plusD, Pi.single_apply, hij, hij.symm]
  try linear_combination two_eq_zero_K (K := K)

theorem s16k_dot_plusB_plusA [CharP K 2] {i j : Fin m} (hij : i ≠ j) :
    plusB i j ⬝ᵥ (plusM m K *ᵥ plusA j) = 0 := by
  unfold plusB plusA
  rw [add_dotProduct, add_dotProduct, s16k_single_inl_dot, s16k_single_inl_dot,
    s16k_single_inr_dot]
  simp [Pi.single_apply, hij, hij.symm]
  try linear_combination two_eq_zero_K (K := K)

theorem s16k_dot_plusB_plusD [CharP K 2] {i j : Fin m} (hij : i ≠ j) :
    plusB i j ⬝ᵥ (plusM m K *ᵥ s16k_plusD (K := K) i j) = 0 := by
  unfold plusB
  rw [add_dotProduct, add_dotProduct, s16k_single_inl_dot, s16k_single_inl_dot,
    s16k_single_inr_dot]
  simp [s16k_plusD, Pi.single_apply, hij, hij.symm]
  try linear_combination two_eq_zero_K (K := K)

theorem s16k_plusD_apply_eq_zero {i j : Fin m} {r : Fin m ⊕ Fin m}
    (hi : plusIdx r ≠ i) (hj : plusIdx r ≠ j) :
    (s16k_plusD (K := K) i j) r = 0 := by
  rcases r with c | c <;> simp_all [plusIdx, s16k_plusD]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
