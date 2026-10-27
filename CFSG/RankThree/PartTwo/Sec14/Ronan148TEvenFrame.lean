module

public import CFSG.RankThree.PartTwo.Sec14.Ronan148TEvenBlock

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148T

open Matrix CFSG.RankThree.PartTwo.Sec16.KL3SubProof

variable {F : Type} [Field F]

theorem mul_same_axis {p q ℓ : Fin 3 → F} (hℓq : ℓ ⬝ᵥ q = 0) (c : F) :
    (1 + vecMulVec p ℓ) * (1 + c • vecMulVec q ℓ) =
      (1 + vecMulVec (p + c • q) ℓ : Matrix (Fin 3) (Fin 3) F) := by
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.mul_smul,
    vecMulVec_mul_vecMulVec, hℓq, zero_smul, vecMulVec_zero, smul_zero, add_zero, add_vecMulVec,
    smul_vecMulVec]
  abel

theorem mul_same_center {p ℓ ℓ' : Fin 3 → F} (hℓp : ℓ ⬝ᵥ p = 0) (c : F) :
    (1 + vecMulVec p ℓ) * (1 + c • vecMulVec p ℓ') =
      (1 + vecMulVec p (ℓ + c • ℓ') : Matrix (Fin 3) (Fin 3) F) := by
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.mul_smul,
    vecMulVec_mul_vecMulVec, hℓp, zero_smul, vecMulVec_zero, smul_zero, add_zero, vecMulVec_add,
    vecMulVec_smul]
  abel

theorem isElat_of_frame {e f : Fin 3 → Fin 3 → F} (h : IsFrame e f) {i j : Fin 3} (hij : i ≠ j)
    {g : GL (Fin 3) F} (hg : (g : Matrix (Fin 3) (Fin 3) F) = 1 + vecMulVec (e i) (f j)) :
    IsElat g (e i) (f j) := by
  refine ⟨?_, ?_, ?_, hg⟩
  · intro h0
    have := h i i
    rw [h0, dotProduct_zero, if_pos rfl] at this
    exact zero_ne_one this
  · intro h0
    have := h j j
    rw [h0, zero_dotProduct, if_pos rfl] at this
    exact zero_ne_one this
  · rw [h j i, if_neg (Ne.symm hij)]

theorem exists_frame [CharP F 2] {D : Subgroup (GL (Fin 3) F)} {K₀ : Subfield F}
    (hR : ∀ z ∈ D, ∀ p ℓ : Fin 3 → F, IsElat z p ℓ → rootSet D p ℓ = K₀)
    (hν : ∀ z ∈ D, ∀ w ∈ D, ∀ p ℓ b ψ : Fin 3 → F, IsElat z p ℓ → IsElat w b ψ → ℓ ⬝ᵥ b ≠ 0 →
      ψ ⬝ᵥ p ≠ 0 → (ℓ ⬝ᵥ b) * (ψ ⬝ᵥ p) ∈ K₀)
    {r u s t : GL (Fin 3) F} (hr : r ∈ D) (hu : u ∈ D) (hs : s ∈ D) (ht : t ∈ D)
    {a φ b ψ a' ψ' : Fin 3 → F} (hrE : IsElat r a φ) (huE : IsElat u b ψ)
    (hsE : IsElat s a' φ) (htE : IsElat t a ψ') (hφb : φ ⬝ᵥ b ≠ 0) (hψa : ψ ⬝ᵥ a ≠ 0)
    (ha' : ψ' ⬝ᵥ a' ≠ 0) :
    ∃ e f : Fin 3 → Fin 3 → F, IsFrame e f ∧
      ∀ i j, i ≠ j → ∃ g ∈ D, (g : Matrix (Fin 3) (Fin 3) F) = 1 + vecMulVec (e i) (f j) := by
  have two : (2 : F) = 0 := CharTwo.two_eq_zero
  have hφa := hrE.2.2.1
  have hψb := huE.2.2.1
  have hφa' := hsE.2.2.1
  have hψ'a := htE.2.2.1
  have hmem : ∀ {z : GL (Fin 3) F} {p ℓ : Fin 3 → F}, z ∈ D → IsElat z p ℓ → ∀ c ∈ K₀,
      ∃ g ∈ D, (g : Matrix (Fin 3) (Fin 3) F) = 1 + c • vecMulVec p ℓ := by
    intro z p ℓ hz hzE c hc
    have : c ∈ rootSet D p ℓ := by rw [hR z hz p ℓ hzE]; exact hc
    exact this
  set ν := (φ ⬝ᵥ b) * (ψ ⬝ᵥ a) with hνdef
  have hν0 : ν ≠ 0 := mul_ne_zero hφb hψa
  have hνK : ν ∈ K₀ := hν r hr u hu a φ b ψ hrE huE hφb hψa
  set α := (ψ ⬝ᵥ a') / (ψ ⬝ᵥ a) with hαdef
  have hαK : α ∈ K₀ := by
    by_cases h : ψ ⬝ᵥ a' = 0
    · rw [hαdef, h, zero_div]
      exact K₀.zero_mem
    · have h1 := hν u hu s hs b ψ a' φ huE hsE h hφb
      have : α = (ψ ⬝ᵥ a') * (φ ⬝ᵥ b) / ν := by
        rw [hαdef, hνdef]
        field_simp
      rw [this]
      exact K₀.div_mem h1 hνK
  set η₁ := (φ ⬝ᵥ b)⁻¹ * (ψ' ⬝ᵥ b) with hη₁def
  have hη₁K : η₁ ∈ K₀ := by
    by_cases h : ψ' ⬝ᵥ b = 0
    · rw [hη₁def, h, mul_zero]
      exact K₀.zero_mem
    · have h1 := hν u hu t ht b ψ a ψ' huE htE hψa h
      have : η₁ = (ψ ⬝ᵥ a) * (ψ' ⬝ᵥ b) / ν := by
        rw [hη₁def, hνdef]
        field_simp
      rw [this]
      exact K₀.div_mem h1 hνK
  set η₂ := ψ' ⬝ᵥ a' with hη₂def
  set e : Fin 3 → Fin 3 → F := ![a, (φ ⬝ᵥ b)⁻¹ • b, a' + α • a] with hedef
  set f : Fin 3 → Fin 3 → F := ![(ψ ⬝ᵥ a)⁻¹ • ψ, φ, η₂⁻¹ • (ψ' + η₁ • φ)] with hfdef
  have he0 : e 0 = a := rfl
  have he1 : e 1 = (φ ⬝ᵥ b)⁻¹ • b := rfl
  have he2 : e 2 = a' + α • a := rfl
  have hf0 : f 0 = (ψ ⬝ᵥ a)⁻¹ • ψ := rfl
  have hf1 : f 1 = φ := rfl
  have hf2 : f 2 = η₂⁻¹ • (ψ' + η₁ • φ) := rfl
  have hψa'α : ψ ⬝ᵥ a' + α * (ψ ⬝ᵥ a) = 0 := by
    rw [hαdef, div_mul_cancel₀ _ hψa]
    linear_combination (ψ ⬝ᵥ a') * two
  have hfr : IsFrame e f := by
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue, he0, he1, he2, hf0, hf1,
        hf2, smul_dotProduct, dotProduct_smul, dotProduct_add, add_dotProduct, smul_eq_mul,
        hφa, hψb, hφa', hψ'a, if_true, if_false, Fin.reduceEq, ne_eq, not_false_eq_true,
        reduceCtorEq] <;> norm_num
    · exact inv_mul_cancel₀ hψa
    · linear_combination (ψ ⬝ᵥ a)⁻¹ * hψa'α
    · exact inv_mul_cancel₀ hφb
    · right; right
      rw [hη₁def, mul_comm (φ ⬝ᵥ b)⁻¹, mul_assoc, inv_mul_cancel₀ hφb, mul_one]
      linear_combination (ψ' ⬝ᵥ b) * two
    · rw [← hη₂def]
      exact inv_mul_cancel₀ ha'
  have hd : ∀ i j : Fin 3, i ≠ j → f i ⬝ᵥ e j = 0 := fun i j hij => by rw [hfr i j, if_neg hij]
  have hd1 : ∀ i : Fin 3, f i ⬝ᵥ e i = 1 := fun i => by rw [hfr i i, if_pos rfl]
  have hsq : ∀ {g₁ g₂ : GL (Fin 3) F} {i j k : Fin 3}, g₁ ∈ D → g₂ ∈ D →
      (g₁ : Matrix (Fin 3) (Fin 3) F) = 1 + vecMulVec (e i) (f j) →
      (g₂ : Matrix (Fin 3) (Fin 3) F) = 1 + vecMulVec (e k) (f i) → i ≠ j → j ≠ k → k ≠ i →
      ∃ g ∈ D, (g : Matrix (Fin 3) (Fin 3) F) = 1 + vecMulVec (e k) (f j) := by
    intro g₁ g₂ i j k hg₁ hg₂ hg₁m hg₂m hij hjk hki
    refine ⟨g₁ * g₂ * (g₁ * g₂), D.mul_mem (D.mul_mem hg₁ hg₂) (D.mul_mem hg₁ hg₂), ?_⟩
    simp only [Units.val_mul]
    rw [hg₁m, hg₂m, sq_mul_of_dotProduct_eq_zero (hd j i (Ne.symm hij)) (hd i k (Ne.symm hki))
      (hd j k hjk), hd1, one_smul]
  have hX01 : ∃ g ∈ D, (g : Matrix (Fin 3) (Fin 3) F) = 1 + vecMulVec (e 0) (f 1) :=
    ⟨r, hr, by rw [he0, hf1]; exact hrE.2.2.2⟩
  have hX10 : ∃ g ∈ D, (g : Matrix (Fin 3) (Fin 3) F) = 1 + vecMulVec (e 1) (f 0) := by
    obtain ⟨g, hg, hgm⟩ := hmem hu huE ν⁻¹ (K₀.inv_mem hνK)
    refine ⟨g, hg, ?_⟩
    rw [hgm, he1, hf0, smul_vecMulVec, vecMulVec_smul, smul_smul, hνdef, mul_inv]
  have hX21 : ∃ g ∈ D, (g : Matrix (Fin 3) (Fin 3) F) = 1 + vecMulVec (e 2) (f 1) := by
    obtain ⟨g, hg, hgm⟩ := hmem hr hrE α hαK
    refine ⟨s * g, D.mul_mem hs hg, ?_⟩
    rw [Units.val_mul, hsE.2.2.2, hgm, mul_same_axis hφa, he2, hf1]
  obtain ⟨g10, hg10, hg10m⟩ := hX10
  obtain ⟨g21, hg21, hg21m⟩ := hX21
  have hX20 := hsq hg10 hg21 hg10m hg21m (by decide) (by decide) (by decide)
  obtain ⟨g20, hg20, hg20m⟩ := hX20
  obtain ⟨gη, hgη, hgηm⟩ := hmem hr hrE η₁ hη₁K
  have hy02m : ((t * gη : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      1 + vecMulVec (e 0) (η₂ • f 2) := by
    rw [Units.val_mul, htE.2.2.2, hgηm, mul_same_center hψ'a, he0, hf2, smul_smul,
      mul_inv_cancel₀ ha', one_smul]
  have hy02E : IsElat (t * gη) (e 0) (η₂ • f 2) := by
    refine ⟨?_, ?_, ?_, hy02m⟩
    · rw [he0]; exact hrE.1
    · intro h0
      have := congrArg (fun v => v ⬝ᵥ e 2) h0
      simp only [smul_dotProduct, hd1, smul_eq_mul, mul_one, zero_dotProduct] at this
      exact ha' this
    · rw [smul_dotProduct, hd 2 0 (by decide), smul_zero]
  have hy02 : t * gη ∈ D := D.mul_mem ht hgη
  have hη₂K : η₂ ∈ K₀ := by
    have h1 := hν _ hy02 _ hg20 _ _ _ _ hy02E (isElat_of_frame hfr (by decide) hg20m)
      (by rw [smul_dotProduct, hd1, smul_eq_mul, mul_one]; exact ha')
      (by rw [hd1]; exact one_ne_zero)
    rwa [smul_dotProduct, hd1, hd1, smul_eq_mul, mul_one, mul_one] at h1
  have hX02 : ∃ g ∈ D, (g : Matrix (Fin 3) (Fin 3) F) = 1 + vecMulVec (e 0) (f 2) := by
    obtain ⟨g, hg, hgm⟩ := hmem hy02 hy02E η₂⁻¹ (K₀.inv_mem hη₂K)
    refine ⟨g, hg, ?_⟩
    rw [hgm, vecMulVec_smul, smul_smul, inv_mul_cancel₀ ha', one_smul]
  obtain ⟨g02, hg02, hg02m⟩ := hX02
  have hX12 := hsq hg02 hg10 hg02m hg10m (by decide) (by decide) (by decide)
  refine ⟨e, f, hfr, ?_⟩
  intro i j hij
  fin_cases i <;> fin_cases j
  · exact absurd rfl hij
  · exact hX01
  · exact ⟨g02, hg02, hg02m⟩
  · exact ⟨g10, hg10, hg10m⟩
  · exact absurd rfl hij
  · exact hX12
  · exact ⟨g20, hg20, hg20m⟩
  · exact ⟨g21, hg21, hg21m⟩
  · exact absurd rfl hij

end CFSG.RankThree.PartTwo.Sec14.Ronan148T
