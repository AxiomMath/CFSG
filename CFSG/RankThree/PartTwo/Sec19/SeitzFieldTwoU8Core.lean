module

public import CFSG.RankThree.PartTwo.Sec19.SeitzFieldTwoU8Sound
public import Certificates.Certificate188005
public import CFSG.RankThree.PartTwo.KFacts.K71SU3
public import CFSG.RankThree.PartTwo.Sec19.Item19Res6ProofUnitaryArith
public import CFSG.RankThree.PartTwo.Sec19.Item19Res5ProofFaithRank

public section

namespace CFSG.RankThree.PartTwo.Sec19.U38F

open CFSG.LieType.SeitzGeneration CFSG.LieType.SeitzGeneration.HeisSmall HuppertU38F
open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial Matrix
open CFSG.GH74.GLS.IVK (fixedField mem_fixedField_iff)
open CFSG.RankThree.PartTwo.KFacts

variable {K : Type} [Field K]

theorem pow_four_of_fixed (h : UnitaryFieldData 2 3 K) {σ : K ≃+* K} (hσ : orderOf σ = 3) {x : K}
    (hx : σ x = x) : x ^ 4 = x := by
  have := h.finite
  obtain ⟨f₀, hf, hf1, hcard⟩ := exists_card_fixedField_of_orderOf_eq_three h hσ
  have hf₀ : f₀ = 1 := by omega
  subst hf₀
  have : Fintype (fixedField σ) := Fintype.ofFinite _
  have hxk : x ∈ fixedField σ := (mem_fixedField_iff σ x).2 hx
  have h1 := FiniteField.pow_card (⟨x, hxk⟩ : fixedField σ)
  rw [← Nat.card_eq_fintype_card, hcard] at h1
  have h2 := congrArg (fun y : fixedField σ => (y : K)) h1
  simpa using h2

theorem four_cases {ω x : K} (hω : IsPrimitiveRoot ω 3) (hx : x ^ 4 = x) :
    x = 0 ∨ x = 1 ∨ x = ω ∨ x = ω ^ 2 := by
  have hω3 : ω ^ 3 = 1 := hω.pow_eq_one
  have hω1 : ω ≠ 1 := hω.ne_one (by norm_num)
  have hq : ω ^ 2 + ω + 1 = 0 := by
    have h1 : (ω - 1) * (ω ^ 2 + ω + 1) = 0 := by linear_combination hω3
    exact (mul_eq_zero.1 h1).resolve_left (sub_ne_zero.2 hω1)
  have hfac : x * ((x - 1) * ((x - ω) * (x - ω ^ 2))) = 0 := by
    linear_combination hx - x ^ 2 * (x - 1) * hq + x * (x - 1) * hω3
  rcases mul_eq_zero.1 hfac with h0 | h0
  · exact Or.inl h0
  rcases mul_eq_zero.1 h0 with h1 | h1
  · exact Or.inr (Or.inl (sub_eq_zero.1 h1))
  rcases mul_eq_zero.1 h1 with h2 | h2
  · exact Or.inr (Or.inr (Or.inl (sub_eq_zero.1 h2)))
  · exact Or.inr (Or.inr (Or.inr (sub_eq_zero.1 h2)))

theorem exists_l4 (ι : Q8 →+* K) {ω : K} (hιω : ι w0 = ω) {x : K}
    (hx : x = 0 ∨ x = 1 ∨ x = ω ∨ x = ω ^ 2) : ∃ a ∈ l4, ι a = x := by
  rcases hx with rfl | rfl | rfl | rfl
  · exact ⟨0, by simp [l4], map_zero ι⟩
  · exact ⟨1, by simp [l4], map_one ι⟩
  · exact ⟨w0, by simp [l4], hιω⟩
  · exact ⟨w0 * w0, by simp [l4], by rw [map_mul, hιω, sq]⟩

theorem exists_model_matrix (ι : Q8 →+* K) {ω : K} (hιω : ι w0 = ω) (hω : IsPrimitiveRoot ω 3)
    {B : Matrix (Fin 3) (Fin 3) K} (hB : ∀ i j, B i j ^ 4 = B i j) :
    ∃ Ym : M3 Q8, entriesL4 Ym = true ∧ toMat ι Ym = B := by
  have key : ∀ i j, ∃ a ∈ l4, ι a = B i j := fun i j =>
    exists_l4 ι hιω (four_cases hω (hB i j))
  choose A hA hAι using key
  refine ⟨⟨A 0 0, A 0 1, A 0 2, A 1 0, A 1 1, A 1 2, A 2 0, A 2 1, A 2 2⟩, ?_, ?_⟩
  · exact decide_eq_true ⟨hA 0 0, hA 0 1, hA 0 2, hA 1 0, hA 1 1, hA 1 2, hA 2 0, hA 2 1, hA 2 2⟩
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [toMat, hAι]

theorem bar_mul_self_cases (h : UnitaryFieldData 2 3 K) {x : K} (hx : x ^ 4 = x) :
    h.bar x * x = 0 ∨ h.bar x * x = 1 := by
  rw [UnitaryFieldData.bar_apply]
  have h9 : x ^ 2 ^ 3 * x = x ^ 3 := by
    calc x ^ 2 ^ 3 * x = (x ^ 4) ^ 2 * x := by ring
      _ = x ^ 2 * x := by rw [hx]
      _ = x ^ 3 := by ring
  rw [h9]
  by_cases h0 : x = 0
  · left
    rw [h0]
    norm_num
  · right
    have h1 : x * (x ^ 3 - 1) = 0 := by linear_combination hx
    exact sub_eq_zero.1 ((mul_eq_zero.1 h1).resolve_left h0)

theorem sum01 {a b c : K} (h2 : (2 : K) = 0) (ha : a = 0 ∨ a = 1) (hb : b = 0 ∨ b = 1)
    (hc : c = 0 ∨ c = 1) : a + b + c = 0 ∨ a + b + c = 1 := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> rcases hc with rfl | rfl
  · left
    ring
  · right
    ring
  · right
    ring
  · left
    linear_combination h2
  · right
    ring
  · left
    linear_combination h2
  · left
    linear_combination h2
  · right
    linear_combination h2

theorem unitary_normalize (h : UnitaryFieldData 2 3 K) {M B' : Matrix (Fin 3) (Fin 3) K} {b : K}
    (hb : b ≠ 0) (hB' : B' = b⁻¹ • M) (hMu : (M.map h.bar)ᵀ * M = 1)
    (hfour : ∀ i j, B' i j ^ 4 = B' i j) : (B'.map h.bar)ᵀ * B' = 1 := by
  have h2 : (2 : K) = 0 := by
    have := h.charP
    exact_mod_cast CharP.cast_eq_zero K 2
  have hbb : h.bar b ≠ 0 := (map_ne_zero h.bar).2 hb
  have hM : ∀ i j, M i j = b * B' i j := fun i j => by
    rw [hB']
    simp [Matrix.smul_apply, hb]
  have e00 := congrFun (congrFun hMu 0) 0
  simp only [Matrix.mul_apply, Fin.sum_univ_three, Matrix.transpose_apply, Matrix.map_apply,
    Matrix.one_apply_eq] at e00
  have hn : (h.bar b * b) * (h.bar (B' 0 0) * B' 0 0 + h.bar (B' 1 0) * B' 1 0 +
      h.bar (B' 2 0) * B' 2 0) = 1 := by
    rw [← e00]
    simp only [hM, map_mul]
    ring
  have hs01 := sum01 h2 (bar_mul_self_cases h (hfour 0 0)) (bar_mul_self_cases h (hfour 1 0))
    (bar_mul_self_cases h (hfour 2 0))
  have hn1 : h.bar b * b = 1 := by
    rcases hs01 with hs | hs
    · rw [hs, mul_zero] at hn
      exact absurd hn zero_ne_one
    · rwa [hs, mul_one] at hn
  have hsum : ∀ i j, ∑ k, h.bar (B' k i) * B' k j =
      (h.bar b * b)⁻¹ * ∑ k, h.bar (M k i) * M k j := by
    intro i j
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    rw [hM k i, hM k j, map_mul]
    field_simp
  ext i j
  have hij := congrFun (congrFun hMu i) j
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply] at hij ⊢
  rw [hsum, hn1, inv_one, one_mul]
  exact hij

theorem toMat_inj (ι : Q8 →+* K) {A B : M3 Q8} (h : toMat ι A = toMat ι B) : A = B := by
  have e := fun i j => congrFun (congrFun h i) j
  apply M3.ext <;> apply ι.injective
  · simpa [toMat] using e 0 0
  · simpa [toMat] using e 0 1
  · simpa [toMat] using e 0 2
  · simpa [toMat] using e 1 0
  · simpa [toMat] using e 1 1
  · simpa [toMat] using e 1 2
  · simpa [toMat] using e 2 0
  · simpa [toMat] using e 2 1
  · simpa [toMat] using e 2 2

theorem isScalar_of_toMat (ι : Q8 →+* K) {A : M3 Q8} {d : K}
    (h : toMat ι A = d • (1 : Matrix (Fin 3) (Fin 3) K)) : isScalar A = true := by
  have e := fun i j => congrFun (congrFun h i) j
  have e01 := e 0 1
  have e02 := e 0 2
  have e10 := e 1 0
  have e12 := e 1 2
  have e20 := e 2 0
  have e21 := e 2 1
  have e00 := e 0 0
  have e11 := e 1 1
  have e22 := e 2 2
  simp [toMat] at e01 e02 e10 e12 e20 e21 e00 e11 e22
  refine decide_eq_true ⟨ι.injective (by rw [e01, map_zero]), ι.injective (by rw [e02, map_zero]),
    ι.injective (by rw [e10, map_zero]), ι.injective (by rw [e12, map_zero]),
    ι.injective (by rw [e20, map_zero]), ι.injective (by rw [e21, map_zero]),
    ι.injective (by rw [e11, e00]), ι.injective (by rw [e22, e00])⟩

theorem toMat_scalar_of_isScalar (ι : Q8 →+* K) {A : M3 Q8} (h : isScalar A = true) :
    toMat ι A = ι A.a00 • (1 : Matrix (Fin 3) (Fin 3) K) := by
  obtain ⟨h01, h02, h10, h12, h20, h21, h11, h22⟩ := of_decide_eq_true h
  ext i j
  fin_cases i <;> fin_cases j <;> simp [toMat, h01, h02, h10, h12, h20, h21, h11, h22]

theorem isPrimitiveRoot_w0 : IsPrimitiveRoot w0 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h := orderOf_eq_prime (QExt.omega_pow_three (F := GF8)) QExt.omega_ne_one
  rw [← h]
  exact IsPrimitiveRoot.orderOf _

theorem exists_ne_zero_entry {M : Matrix (Fin 3) (Fin 3) K} (hM : ¬ ∃ c : K, M = c • 1) :
    ∃ i j, M i j ≠ 0 := by
  by_contra hcon
  push_neg at hcon
  apply hM
  exact ⟨0, by ext i j; simp [hcon i j]⟩

theorem eq_top_of_fixed_cent (h : UnitaryFieldData 2 3 K)
    {σ : K ≃+* K} (hσ : orderOf σ = 3) (Q : Subgroup (unitarySU 2 3 K 3))
    (hR : ∀ g : unitarySU 2 3 K 3, (∀ i j, σ (((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) i j) =
      ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) i j) → g ∈ Q)
    {B : GL (Fin 3) K} (hB : B ∈ unitaryIsom3 h)
    (hBσ : ∃ c : K, ((B : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).map σ =
      c • ((B : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K))
    (hBn : ¬ ∃ c : K, ((B : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = c • 1)
    (hB3 : ∃ c : K, ((B : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
      ((B : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * ((B : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
        c • 1)
    (hC : ∀ g : unitarySU 2 3 K 3, ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
      ((B : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = ((B : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
        ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) → g ∈ Q) : Q = ⊤ := by
  have := h.finite
  obtain ⟨M, hMdef⟩ : ∃ M : Matrix (Fin 3) (Fin 3) K, M = ((B : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) :=
    ⟨_, rfl⟩
  rw [← hMdef] at hBσ hBn hB3 hC
  have hMu : (M.map h.bar)ᵀ * M = 1 := by rw [hMdef]; exact hB
  have hσ3 : σ ^ 3 = 1 := by rw [← hσ]; exact pow_orderOf_eq_one σ
  have hK3 : 3 ∣ Nat.card K - 1 := by rw [h.card]; norm_num
  obtain ⟨ω, hω⟩ := Item19Res5Proof.exists_isPrimitiveRoot_three hK3
  obtain ⟨ι, hι, hιω⟩ := exists_ringHom_omega (L := Q8) h (by norm_num)
    (by rw [card_q8]; norm_num) isPrimitiveRoot_w0 hω
  have hσω : σ (ι w0) = ι w0 := by
    rw [hιω]
    exact CFSG.RankThree.PartTwo.Sec19.Item19Res6Proof.ringEquiv_fix_of_cube hσ3 hω.pow_eq_one
  have hq : 2 ^ 3 = 8 := by norm_num
  obtain ⟨i0, j0, hb⟩ := exists_ne_zero_entry hBn
  obtain ⟨c, hc⟩ := hBσ
  have hcb : σ (M i0 j0) = c * M i0 j0 := by
    have := congrFun (congrFun hc i0) j0
    simpa [Matrix.map_apply, Matrix.smul_apply] using this
  have hc0 : c ≠ 0 := by
    intro hc0
    rw [hc0, zero_mul] at hcb
    exact hb (σ.injective (by rw [hcb, map_zero]))
  obtain ⟨B', hB'⟩ : ∃ B' : Matrix (Fin 3) (Fin 3) K, B' = (M i0 j0)⁻¹ • M := ⟨_, rfl⟩
  have hMB' : M = M i0 j0 • B' := by rw [hB', smul_inv_smul₀ hb]
  have hfix : ∀ i j, σ (B' i j) = B' i j := by
    intro i j
    have hij := congrFun (congrFun hc i) j
    simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul] at hij
    rw [hB']
    simp only [Matrix.smul_apply, smul_eq_mul, map_mul, map_inv₀, hij, hcb]
    field_simp
  have hfour : ∀ i j, B' i j ^ 4 = B' i j := fun i j => pow_four_of_fixed h hσ (hfix i j)
  have hu : (B'.map h.bar)ᵀ * B' = 1 := unitary_normalize h hb hB' hMu hfour
  obtain ⟨Ym, hYe, hYm⟩ := exists_model_matrix ι hιω hω hfour
  have hYu : unitaryOk Ym = true := by
    apply decide_eq_true
    apply toMat_inj ι
    rw [toMat_mul, toMat_one]
    have h1 := toMat_transpose_map h ι Ym
    rw [hq] at h1
    rw [h1, hYm, hu]
  have hYns : isScalar Ym = false := by
    by_contra hcon
    have h1 := toMat_scalar_of_isScalar ι (Bool.eq_true_of_not_eq_false hcon)
    apply hBn
    refine ⟨M i0 j0 * ι Ym.a00, ?_⟩
    calc M = M i0 j0 • B' := hMB'
      _ = (M i0 j0 * ι Ym.a00) • 1 := by rw [← hYm, h1, smul_smul]
  have hY3 : isScalar (Ym * Ym * Ym) = true := by
    obtain ⟨c3, hc3⟩ := hB3
    apply isScalar_of_toMat ι (d := (M i0 j0)⁻¹ ^ 3 * c3)
    rw [toMat_mul, toMat_mul, hYm, hB']
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    rw [hc3, smul_smul]
    ring_nf
  have hCY : ∀ g : unitarySU 2 3 K 3, ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * toMat ι Ym =
      toMat ι Ym * ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) → g ∈ Q := by
    intro g hg
    apply hC g
    rw [hYm, hB', Matrix.mul_smul, Matrix.smul_mul] at hg
    exact smul_right_injective _ (inv_ne_zero hb) hg
  exact eq_top_of_class h hq ι hι hσω Certificates.certificate188005 hYe hYu hYns hY3 Q hR hCY

end CFSG.RankThree.PartTwo.Sec19.U38F
