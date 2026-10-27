module

public import CFSG.Quasithin.Vol2.Ch3E213MG41SZ3
public import CFSG.Quasithin.Vol2.Ch3E213MG41SZ7
public import CFSG.Quasithin.Vol2.Ch3E213MP6BD

public section

namespace CFSG.Quasithin.Ch3E213M

open CFSG.ComponentClassification.UnbalancedCatalog.SpChain
  (antiSp glMat uElt minorJ mem_antiSp transpose_mul_minorJ_mul_apply minorJ_apply)
open CFSG.Quasithin.SteinbergBS (upper_of_mem_normalizer)

namespace G41.CTwo

variable {k : Type} [Field k]

@[expose] noncomputable def diagElt (t₀ t₁ : k) (h₀ : t₀ ≠ 0) (h₁ : t₁ ≠ 0) : antiSp k :=
  ⟨⟨Matrix.diagonal ![t₀, t₁, t₁⁻¹, t₀⁻¹], Matrix.diagonal ![t₀⁻¹, t₁⁻¹, t₁, t₀],
    by
      rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
      congr 1
      funext i
      fin_cases i <;> simp [h₀, h₁],
    by
      rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
      congr 1
      funext i
      fin_cases i <;> simp [h₀, h₁]⟩,
    by
      rw [mem_antiSp]
      change Matrix.transpose (Matrix.diagonal ![t₀, t₁, t₁⁻¹, t₀⁻¹]) * minorJ k *
        Matrix.diagonal ![t₀, t₁, t₁⁻¹, t₀⁻¹] = minorJ k
      ext i j
      rw [transpose_mul_minorJ_mul_apply, minorJ_apply]
      fin_cases i <;> fin_cases j <;> simp [h₀, h₁]⟩

theorem glMat_diagElt (t₀ t₁ : k) (h₀ : t₀ ≠ 0) (h₁ : t₁ ≠ 0) :
    glMat (diagElt t₀ t₁ h₀ h₁ : GL (Fin 4) k) = Matrix.diagonal ![t₀, t₁, t₁⁻¹, t₀⁻¹] :=
  rfl

theorem isUpper_diagElt (t₀ t₁ : k) (h₀ : t₀ ≠ 0) (h₁ : t₁ ≠ 0) :
    IsUpper (diagElt t₀ t₁ h₀ h₁) := fun i j hij => by
  rw [glMat_diagElt, Matrix.diagonal_apply_ne _ (ne_of_gt hij)]

end G41.CTwo

open G41.CTwo

theorem factSp4CTwo_holds : FactSp4CTwo := by
  intro k _ _ _ _ _ _ W hWZ _ hsp hσex g hg hT hT'
  obtain ⟨h, hhN, _, ⟨r, rfl⟩, hσ⟩ := hσex
  have hh : IsUpper h := upper_of_mem_normalizer hhN
  have hWI : W ≤ W ⊔ W.map (MulAut.conj g).toMonoidHom := le_sup_left
  have hWgI : ∀ w ∈ W, g * w * g⁻¹ ∈ W ⊔ W.map (MulAut.conj g).toMonoidHom :=
    fun w hw => (le_sup_right : W.map (MulAut.conj g).toMonoidHom ≤ _) ⟨w, hw, rfl⟩
  obtain ⟨b₁, c₁, b₂, c₂, h₁W, h₂W, hb₁, hdet⟩ := P6B.exists_indep hWZ hsp
  set S := centreSystem hg hT hT' hb₁ (hWI h₁W) (hWgI _ h₁W) with hS
  have hSb : S.b₀ = b₁ := rfl
  have hSc : S.c₀ = c₁ := rfl
  have hQP : ∀ {b c : k}, uElt 0 b c 0 ∈ W → S.P b c := fun hw => hWI hw
  have hb₂ : b₂ ≠ 0 := by
    intro h0
    have hc0 := (eq_zero_iff_of_mem hT hT' (hWI h₂W)).mp h0
    exact hdet (by rw [h0, hc0]; ring)
  have hb₁₂ : b₁ ≠ b₂ := by
    intro h0
    have hc0 : c₁ = c₂ := S.eq_of_P (hQP h₁W) (by rw [h0]; exact hQP h₂W)
    exact hdet (by rw [h0, hc0]; ring)
  have hh₁ : glMat (h : GL (Fin 4) k) 0 0 * glMat (h : GL (Fin 4) k) 1 1 ≠ 0 :=
    mul_ne_zero (isUpper_diag_ne_zero hh 0) (isUpper_diag_ne_zero hh 1)
  have hσ' : ∀ {b c : k}, uElt 0 b c 0 ∈ W →
      uElt 0 (glMat (h : GL (Fin 4) k) 0 0 * glMat (h : GL (Fin 4) k) 1 1 * c ^ 2 ^ r)
        (glMat (h : GL (Fin 4) k) 0 0 ^ 2 * (b ^ 2 ^ r) ^ 2) 0 ∈ W := fun {b c} hw => by
    have := hσ _ hw
    rwa [P6B.sigma_uElt_center hh] at this
  obtain ⟨F₁, a, ha, hcard, hshape⟩ :=
    S.exists_suzuki_shape (Q := fun b c => uElt 0 b c 0 ∈ W) hQP h₁W hh₁ hσ' h₁W h₂W hb₁ hb₂
      hb₁₂
  have hc₁ : c₁ ≠ 0 := S.c₀_ne
  obtain ⟨t₀, ht₀⟩ := FiniteField.isSquare_of_char_two (ringChar.eq k 2) c₁
  have ht₀0 : t₀ ≠ 0 := by
    rintro rfl
    exact hc₁ (by rw [ht₀, mul_zero])
  have hd1 : b₁ / t₀ ≠ 0 := div_ne_zero hb₁ ht₀0
  refine ⟨F₁, a, ha, hcard, diagElt t₀ (b₁ / t₀) ht₀0 hd1, isUpper_diagElt _ _ _ _,
    fun w hw => ?_⟩
  obtain ⟨b, c, rfl⟩ := hWZ hw
  obtain ⟨e, heF, hbe, hce⟩ := hshape hw
  refine Subgroup.mem_map.mpr ⟨uElt 0 e (e ^ 2 ^ (a + 1)) 0, mem_szCentre.mpr ⟨e, heF, rfl⟩, ?_⟩
  rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
    P6B.conj_uElt_center (isUpper_diagElt _ _ _ _), glMat_diagElt, hbe, hce, hSb, hSc]
  simp only [Matrix.diagonal_apply_eq, Matrix.cons_val_zero, Matrix.cons_val_one]
  congr 1
  · rw [mul_div_cancel₀ _ ht₀0]
  · rw [ht₀, sq]

end CFSG.Quasithin.Ch3E213M
