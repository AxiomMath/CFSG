module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328.Rows
import CFSG.ClassicalGroups.Orthogonal.Simple
import CFSG.ClassicalGroups.Orthogonal.OmegaSiegelGen

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328

open CFSG.Open Matrix
open CFSG.ClassicalGroups.Orthogonal
open QuadraticMap
open scoped CharTwo
open CFSG.LieType.Universal.Spin (quadMinus_apply quadMinus polar_quadMinus)

private noncomputable abbrev k328r8g_Q {F : Type} [Field F] (b c : F) :
    QuadraticForm F (Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F) :=
  quadMinus 4 F b c

private abbrev k328r8g_e {F : Type} [Field F] (i : Fin 3) : Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F :=
  Pi.single (Sum.inl i) 1

private abbrev k328r8g_f {F : Type} [Field F] (i : Fin 3) : Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F :=
  Pi.single (Sum.inr (Sum.inl i)) 1

private abbrev k328r8g_u {F : Type} [Field F] : Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F :=
  Pi.single (Sum.inr (Sum.inr 0)) 1

private abbrev k328r8g_v {F : Type} [Field F] : Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F :=
  Pi.single (Sum.inr (Sum.inr 1)) 1

private theorem k328r8g_ofColumns_mulVec_single {F : Type} [Field F] [Fintype F] [DecidableEq F]
    {ι : Type} [Fintype ι] [DecidableEq ι] (img : ι → ι → F) (k : ι) :
    (ofColumns F img) *ᵥ (Pi.single k 1 : ι → F) = img k := by
  rw [Matrix.mulVec_single_one]
  funext i
  simp [ofColumns]

private abbrev k328r8g_zc {F : Type} [Field F] (b c α : F) :
    Fin 3 ⊕ Fin 3 ⊕ Fin 2 → (Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F) :=
  Sum.elim ![k328r8g_e 0 + k328r8g_f 1, k328r8g_f 0 + k328r8g_e 1, k328r8g_e 2]
    (Sum.elim ![k328r8g_e 1, k328r8g_e 0, k328r8g_f 2]
      ![α • k328r8g_u + b⁻¹ • k328r8g_v,
        (c / b) • k328r8g_u + (α + 1) • k328r8g_v])

private abbrev k328r8g_tc {F : Type} [Field F] :
    Fin 3 ⊕ Fin 3 ⊕ Fin 2 → (Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F) :=
  Sum.elim ![k328r8g_e 1, k328r8g_e 0 + k328r8g_e 1, k328r8g_e 2]
    (Sum.elim ![k328r8g_f 0 + k328r8g_f 1, k328r8g_f 0, k328r8g_f 2]
      ![k328r8g_u, k328r8g_v])

private theorem k328r8g_charTwo {F : Type} [Field F] [Fintype F] (hF : Fintype.card F = 8) :
    CharP F 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact charP_of_card_eq_prime_pow (p := 2) (f := 3) (by rw [hF]; norm_num)

private theorem k328r8g_b_ne_zero {F : Type} [Field F] [Fintype F] (hF : Fintype.card F = 8)
    (b c : F) (hbc : ∀ s : F, s ^ 2 + b * s + c ≠ 0) : b ≠ 0 := by
  rintro rfl
  have hch := k328r8g_charTwo hF
  obtain ⟨s, hs⟩ := FiniteField.isSquare_of_char_two (ringChar.eq F 2) c
  have h2 : (2 : F) = 0 := by exact_mod_cast CharP.cast_eq_zero F 2
  apply hbc s
  rw [hs]
  linear_combination (s ^ 2) * h2


private theorem k328r8g_z0_iso {F : Type} [Field F] [Fintype F] [DecidableEq F] [CharP F 2]
    (b c α : F) (hb : b ≠ 0) (hα : α ^ 2 + α = 1 + c / b ^ 2) :
    ∀ w, k328r8g_Q b c (ofColumns F (k328r8g_zc b c α) *ᵥ w) = k328r8g_Q b c w := by
  intro w
  have h0 : (ofColumns F (k328r8g_zc b c α) *ᵥ w) (Sum.inl 0) =
      w (Sum.inl 0) + w (Sum.inr (Sum.inl 1)) := by
    simp [ofColumns, Matrix.mulVec, dotProduct, k328r8g_zc, k328r8g_e, k328r8g_f, k328r8g_u,
      k328r8g_v, Fintype.sum_sum_type, Fin.sum_univ_three]
  have h1 : (ofColumns F (k328r8g_zc b c α) *ᵥ w) (Sum.inl 1) =
      w (Sum.inl 1) + w (Sum.inr (Sum.inl 0)) := by
    simp [ofColumns, Matrix.mulVec, dotProduct, k328r8g_zc, k328r8g_e, k328r8g_f, k328r8g_u,
      k328r8g_v, Fintype.sum_sum_type, Fin.sum_univ_three]
  have h2 : (ofColumns F (k328r8g_zc b c α) *ᵥ w) (Sum.inl 2) = w (Sum.inl 2) := by
    simp [ofColumns, Matrix.mulVec, dotProduct, k328r8g_zc, k328r8g_e, k328r8g_f, k328r8g_u,
      k328r8g_v, Fintype.sum_sum_type, Fin.sum_univ_three]
  have h3 : (ofColumns F (k328r8g_zc b c α) *ᵥ w) (Sum.inr (Sum.inl 0)) = w (Sum.inl 1) := by
    simp [ofColumns, Matrix.mulVec, dotProduct, k328r8g_zc, k328r8g_e, k328r8g_f, k328r8g_u,
      k328r8g_v, Fintype.sum_sum_type, Fin.sum_univ_three]
  have h4 : (ofColumns F (k328r8g_zc b c α) *ᵥ w) (Sum.inr (Sum.inl 1)) = w (Sum.inl 0) := by
    simp [ofColumns, Matrix.mulVec, dotProduct, k328r8g_zc, k328r8g_e, k328r8g_f, k328r8g_u,
      k328r8g_v, Fintype.sum_sum_type, Fin.sum_univ_three]
  have h5 : (ofColumns F (k328r8g_zc b c α) *ᵥ w) (Sum.inr (Sum.inl 2)) =
      w (Sum.inr (Sum.inl 2)) := by
    simp [ofColumns, Matrix.mulVec, dotProduct, k328r8g_zc, k328r8g_e, k328r8g_f, k328r8g_u,
      k328r8g_v, Fintype.sum_sum_type, Fin.sum_univ_three]
  have h6 : (ofColumns F (k328r8g_zc b c α) *ᵥ w) (Sum.inr (Sum.inr 0)) =
      α * w (Sum.inr (Sum.inr 0)) + (c / b) * w (Sum.inr (Sum.inr 1)) := by
    simp [ofColumns, Matrix.mulVec, dotProduct, k328r8g_zc, k328r8g_e, k328r8g_f, k328r8g_u,
      k328r8g_v, Fintype.sum_sum_type, Fin.sum_univ_three, div_eq_mul_inv]
  have h7 : (ofColumns F (k328r8g_zc b c α) *ᵥ w) (Sum.inr (Sum.inr 1)) =
      b⁻¹ * w (Sum.inr (Sum.inr 0)) + (α + 1) * w (Sum.inr (Sum.inr 1)) := by
    simp [ofColumns, Matrix.mulVec, dotProduct, k328r8g_zc, k328r8g_e, k328r8g_f, k328r8g_u,
      k328r8g_v, Fintype.sum_sum_type, Fin.sum_univ_three]
  rw [show k328r8g_Q b c (ofColumns F (k328r8g_zc b c α) *ᵥ w) = (quadMinus 4 F b c)
      (ofColumns F (k328r8g_zc b c α) *ᵥ w) from rfl, quadMinus_apply,
    show k328r8g_Q b c w = (quadMinus 4 F b c) w from rfl, quadMinus_apply]
  rw [Fin.sum_univ_three, Fin.sum_univ_three]
  rw [h0, h1, h2, h3, h4, h5, h6, h7]
  rw [div_eq_mul_inv] at hα
  field_simp [hb] at hα ⊢
  have hchar : (2 : F) = 0 := by exact_mod_cast CharP.cast_eq_zero F 2
  have hc : c = (α ^ 2 + α + 1) * b ^ 2 := by
    linear_combination -hα - b ^ 2 * hchar
  rw [hc]
  field_simp [hb] at ⊢
  ring_nf
  simp

private theorem k328r8g_t0_iso {F : Type} [Field F] [Fintype F] [DecidableEq F] [CharP F 2]
    (b c : F) :
    ∀ w, k328r8g_Q b c (ofColumns F k328r8g_tc *ᵥ w) = k328r8g_Q b c w := by
  intro w
  have h0 : (ofColumns F k328r8g_tc *ᵥ w) (Sum.inl 0) = w (Sum.inl 1) := by
    simp [ofColumns, Matrix.mulVec, dotProduct, k328r8g_tc, k328r8g_e, k328r8g_f, k328r8g_u,
      k328r8g_v, Fintype.sum_sum_type, Fin.sum_univ_three]
  have h1 : (ofColumns F k328r8g_tc *ᵥ w) (Sum.inl 1) = w (Sum.inl 0) + w (Sum.inl 1) := by
    simp [ofColumns, Matrix.mulVec, dotProduct, k328r8g_tc, k328r8g_e, k328r8g_f, k328r8g_u,
      k328r8g_v, Fintype.sum_sum_type, Fin.sum_univ_three]
  have h2 : (ofColumns F k328r8g_tc *ᵥ w) (Sum.inl 2) = w (Sum.inl 2) := by
    simp [ofColumns, Matrix.mulVec, dotProduct, k328r8g_tc, k328r8g_e, k328r8g_f, k328r8g_u,
      k328r8g_v, Fintype.sum_sum_type, Fin.sum_univ_three]
  have h3 : (ofColumns F k328r8g_tc *ᵥ w) (Sum.inr (Sum.inl 0)) =
      w (Sum.inr (Sum.inl 0)) + w (Sum.inr (Sum.inl 1)) := by
    simp [ofColumns, Matrix.mulVec, dotProduct, k328r8g_tc, k328r8g_e, k328r8g_f, k328r8g_u,
      k328r8g_v, Fintype.sum_sum_type, Fin.sum_univ_three]
  have h4 : (ofColumns F k328r8g_tc *ᵥ w) (Sum.inr (Sum.inl 1)) = w (Sum.inr (Sum.inl 0)) := by
    simp [ofColumns, Matrix.mulVec, dotProduct, k328r8g_tc, k328r8g_e, k328r8g_f, k328r8g_u,
      k328r8g_v, Fintype.sum_sum_type, Fin.sum_univ_three]
  have h5 : (ofColumns F k328r8g_tc *ᵥ w) (Sum.inr (Sum.inl 2)) = w (Sum.inr (Sum.inl 2)) := by
    simp [ofColumns, Matrix.mulVec, dotProduct, k328r8g_tc, k328r8g_e, k328r8g_f, k328r8g_u,
      k328r8g_v, Fintype.sum_sum_type, Fin.sum_univ_three]
  have h6 : (ofColumns F k328r8g_tc *ᵥ w) (Sum.inr (Sum.inr 0)) = w (Sum.inr (Sum.inr 0)) := by
    simp [ofColumns, Matrix.mulVec, dotProduct, k328r8g_tc, k328r8g_e, k328r8g_f, k328r8g_u,
      k328r8g_v, Fintype.sum_sum_type, Fin.sum_univ_three]
  have h7 : (ofColumns F k328r8g_tc *ᵥ w) (Sum.inr (Sum.inr 1)) = w (Sum.inr (Sum.inr 1)) := by
    simp [ofColumns, Matrix.mulVec, dotProduct, k328r8g_tc, k328r8g_e, k328r8g_f, k328r8g_u,
      k328r8g_v, Fintype.sum_sum_type, Fin.sum_univ_three]
  rw [show k328r8g_Q b c (ofColumns F k328r8g_tc *ᵥ w) = (quadMinus 4 F b c)
      (ofColumns F k328r8g_tc *ᵥ w) from rfl, quadMinus_apply,
    show k328r8g_Q b c w = (quadMinus 4 F b c) w from rfl, quadMinus_apply]
  rw [Fin.sum_univ_three, Fin.sum_univ_three]
  simp only [h0, h1, h2, h3, h4, h5, h6, h7]
  ring_nf
  simp

private abbrev k328r8g_a11 {F : Type} [Field F] : Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F :=
  k328r8g_e 1 + k328r8g_f 1

private abbrev k328r8g_a12 {F : Type} [Field F] : Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F :=
  k328r8g_e 0 + k328r8g_e 1 + k328r8g_f 0

private abbrev k328r8g_a21 {F : Type} [Field F] : Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F :=
  k328r8g_e 0 + k328r8g_e 1 + k328r8g_f 1

private abbrev k328r8g_a22 {F : Type} [Field F] : Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F :=
  k328r8g_f 0 + k328r8g_e 1 + k328r8g_f 1

private def k328r8g_A1 {F : Type} [Field F] (_b _c : F) :
    Submodule F (Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F) :=
  Submodule.span F {k328r8g_a11, k328r8g_a12}

private def k328r8g_A2 {F : Type} [Field F] (_b _c : F) :
    Submodule F (Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F) :=
  Submodule.span F {k328r8g_a21, k328r8g_a22}

private def k328r8g_A3 {F : Type} [Field F] (_b _c : F) :
    Submodule F (Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F) :=
  Submodule.span F {k328r8g_u, k328r8g_v}

private def k328r8g_JJ {F : Type} [Field F] (b c : F) :
    Submodule F (Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F) :=
  k328r8g_A1 b c ⊔ k328r8g_A2 b c ⊔ k328r8g_A3 b c

private theorem k328r8g_mem_JJ_of_mem_A1 {F : Type} [Field F] (b c : F)
    {x : Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F} (hx : x ∈ k328r8g_A1 b c) : x ∈ k328r8g_JJ b c :=
  (le_sup_left : k328r8g_A1 b c ⊔ k328r8g_A2 b c ≤ k328r8g_JJ b c)
    ((le_sup_left : k328r8g_A1 b c ≤ k328r8g_A1 b c ⊔ k328r8g_A2 b c) hx)

private theorem k328r8g_mem_JJ_of_mem_A2 {F : Type} [Field F] (b c : F)
    {x : Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F} (hx : x ∈ k328r8g_A2 b c) : x ∈ k328r8g_JJ b c :=
  (le_sup_left : k328r8g_A1 b c ⊔ k328r8g_A2 b c ≤ k328r8g_JJ b c)
    ((le_sup_right : k328r8g_A2 b c ≤ k328r8g_A1 b c ⊔ k328r8g_A2 b c) hx)

private theorem k328r8g_mem_JJ_of_mem_A3 {F : Type} [Field F] (b c : F)
    {x : Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F} (hx : x ∈ k328r8g_A3 b c) : x ∈ k328r8g_JJ b c :=
  (le_sup_right : k328r8g_A3 b c ≤ k328r8g_JJ b c) hx

private theorem k328r8g_polar_e2_apply {F : Type} [Field F] (b c : F)
    (x : Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F) :
    polar (k328r8g_Q b c) (k328r8g_e 2) x = x (Sum.inr (Sum.inl 2)) :=
  polar_single_inl_quadMinus (n := 4) 2 x

private theorem k328r8g_polar_f2_apply {F : Type} [Field F] (b c : F)
    (x : Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F) :
    polar (k328r8g_Q b c) (k328r8g_f 2) x = x (Sum.inl 2) :=
  polar_single_inr_quadMinus (n := 4) 2 x

private theorem k328r8g_e0_mem_JJ {F : Type} [Field F] [CharP F 2] (b c : F) :
    k328r8g_e (F := F) 0 ∈ k328r8g_JJ b c := by
  have h : k328r8g_e (F := F) 0 = k328r8g_a11 + k328r8g_a21 := by
    funext k
    rcases k with i | i | j
    · fin_cases i <;> simp [k328r8g_a11, k328r8g_a21, k328r8g_e, k328r8g_f]
    · fin_cases i <;> simp [k328r8g_a11, k328r8g_a21, k328r8g_e, k328r8g_f]
    · fin_cases j <;> simp [k328r8g_a11, k328r8g_a21, k328r8g_e, k328r8g_f]
  rw [h]
  exact Submodule.add_mem _
    (k328r8g_mem_JJ_of_mem_A1 b c (Submodule.subset_span (by simp )))
    (k328r8g_mem_JJ_of_mem_A2 b c (Submodule.subset_span (by simp )))

private theorem k328r8g_f0_mem_JJ {F : Type} [Field F] [CharP F 2] (b c : F) :
    k328r8g_f (F := F) 0 ∈ k328r8g_JJ b c := by
  have h : k328r8g_f (F := F) 0 = k328r8g_a11 + k328r8g_a22 := by
    funext k
    rcases k with i | i | j
    · fin_cases i <;> simp [k328r8g_a11, k328r8g_a22, k328r8g_e, k328r8g_f]
    · fin_cases i <;> simp [k328r8g_a11, k328r8g_a22, k328r8g_e, k328r8g_f]
    · fin_cases j <;> simp [k328r8g_a11, k328r8g_a22, k328r8g_e, k328r8g_f]
  rw [h]
  exact Submodule.add_mem _
    (k328r8g_mem_JJ_of_mem_A1 b c (Submodule.subset_span (by simp )))
    (k328r8g_mem_JJ_of_mem_A2 b c (Submodule.subset_span (by simp )))

private theorem k328r8g_e1_mem_JJ {F : Type} [Field F] [CharP F 2] (b c : F) :
    k328r8g_e (F := F) 1 ∈ k328r8g_JJ b c := by
  have h : k328r8g_e (F := F) 1 = k328r8g_a12 + k328r8g_a21 + k328r8g_a22 := by
    funext k
    rcases k with i | i | j
    · fin_cases i <;> simp [k328r8g_a12, k328r8g_a21, k328r8g_a22, k328r8g_e, k328r8g_f]
    · fin_cases i <;> simp [k328r8g_a12, k328r8g_a21, k328r8g_a22, k328r8g_e, k328r8g_f]
    · fin_cases j <;> simp [k328r8g_a12, k328r8g_a21, k328r8g_a22, k328r8g_e, k328r8g_f]
  rw [h]
  exact Submodule.add_mem _
    (Submodule.add_mem _
      (k328r8g_mem_JJ_of_mem_A1 b c (Submodule.subset_span (by simp)))
      (k328r8g_mem_JJ_of_mem_A2 b c (Submodule.subset_span (by simp))))
    (k328r8g_mem_JJ_of_mem_A2 b c (Submodule.subset_span (by simp)))

private theorem k328r8g_f1_mem_JJ {F : Type} [Field F] [CharP F 2] (b c : F) :
    k328r8g_f (F := F) 1 ∈ k328r8g_JJ b c := by
  have h : k328r8g_f (F := F) 1 = k328r8g_a11 + k328r8g_a12 + k328r8g_a21 + k328r8g_a22 := by
    funext k
    rcases k with i | i | j
    · fin_cases i <;> simp [k328r8g_a11, k328r8g_a12, k328r8g_a21, k328r8g_a22, k328r8g_e, k328r8g_f]
    · fin_cases i <;> simp [k328r8g_a11, k328r8g_a12, k328r8g_a21, k328r8g_a22, k328r8g_e, k328r8g_f]
    · fin_cases j <;> simp [k328r8g_a11, k328r8g_a12, k328r8g_a21, k328r8g_a22, k328r8g_e, k328r8g_f]
  rw [h]
  exact Submodule.add_mem _
    (Submodule.add_mem _
      (Submodule.add_mem _
        (k328r8g_mem_JJ_of_mem_A1 b c (Submodule.subset_span (by simp)))
        (k328r8g_mem_JJ_of_mem_A1 b c (Submodule.subset_span (by simp))))
      (k328r8g_mem_JJ_of_mem_A2 b c (Submodule.subset_span (by simp))))
    (k328r8g_mem_JJ_of_mem_A2 b c (Submodule.subset_span (by simp)))

private theorem k328r8g_u_mem_JJ {F : Type} [Field F] (b c : F) :
    k328r8g_u (F := F) ∈ k328r8g_JJ b c :=
  k328r8g_mem_JJ_of_mem_A3 b c (Submodule.subset_span (by simp))

private theorem k328r8g_v_mem_JJ {F : Type} [Field F] (b c : F) :
    k328r8g_v (F := F) ∈ k328r8g_JJ b c :=
  k328r8g_mem_JJ_of_mem_A3 b c (Submodule.subset_span (by simp))


private theorem k328r8g_mem_JJ_of {F : Type} [Field F] [CharP F 2] (b c : F)
    {w : Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F}
    (h1 : w (Sum.inl 2) = 0) (h2 : w (Sum.inr (Sum.inl 2)) = 0) :
    w ∈ k328r8g_JJ b c := by
  have hsum : w = ∑ k, w k • (Pi.single k 1 : Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F) := by
    funext j
    simp [Finset.sum_apply, Pi.single_apply]
  rw [hsum]
  refine Submodule.sum_mem _ fun k _ => ?_
  rcases k with i | i | j
  · fin_cases i
    · exact Submodule.smul_mem _ _ (k328r8g_e0_mem_JJ b c)
    · exact Submodule.smul_mem _ _ (k328r8g_e1_mem_JJ b c)
    · simp [h1]
  · fin_cases i
    · exact Submodule.smul_mem _ _ (k328r8g_f0_mem_JJ b c)
    · exact Submodule.smul_mem _ _ (k328r8g_f1_mem_JJ b c)
    · simp [h2]
  · fin_cases j
    · exact Submodule.smul_mem _ _ (k328r8g_u_mem_JJ b c)
    · exact Submodule.smul_mem _ _ (k328r8g_v_mem_JJ b c)

private theorem k328r8g_perp_e2_le {F : Type} [Field F] [CharP F 2] (b c : F)
    {w : Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F}
    (hw : polar (k328r8g_Q b c) (k328r8g_e 2) w = 0) :
    w ∈ k328r8g_JJ b c ⊔ Submodule.span F ({k328r8g_e 2} : Set
      (Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F)) := by
  have h2 : w (Sum.inr (Sum.inl 2)) = 0 := by
    rw [← k328r8g_polar_e2_apply b c w]; exact hw
  have hw' : w - w (Sum.inl 2) • k328r8g_e 2 ∈ k328r8g_JJ b c := by
    refine k328r8g_mem_JJ_of b c ?_ ?_
    · simp [k328r8g_e, Pi.sub_apply, Pi.smul_apply]
    · simp [h2, k328r8g_e, Pi.sub_apply, Pi.smul_apply]
  have hspan : w (Sum.inl 2) • k328r8g_e 2 ∈
      Submodule.span F ({k328r8g_e 2} : Set (Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F)) :=
    Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton _))
  exact Submodule.mem_sup.mpr ⟨_, hw', _, hspan, sub_add_cancel _ _⟩

private theorem k328r8g_perp_f2_le {F : Type} [Field F] [CharP F 2] (b c : F)
    {w : Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F}
    (hw : polar (k328r8g_Q b c) (k328r8g_f 2) w = 0) :
    w ∈ k328r8g_JJ b c ⊔ Submodule.span F ({k328r8g_f 2} : Set
      (Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F)) := by
  have h2 : w (Sum.inl 2) = 0 := by
    rw [← k328r8g_polar_f2_apply b c w]; exact hw
  have hw' : w - w (Sum.inr (Sum.inl 2)) • k328r8g_f 2 ∈ k328r8g_JJ b c := by
    refine k328r8g_mem_JJ_of b c ?_ ?_
    · simp [h2, k328r8g_f, Pi.sub_apply, Pi.smul_apply]
    · simp [k328r8g_f, Pi.sub_apply, Pi.smul_apply]
  have hspan : w (Sum.inr (Sum.inl 2)) • k328r8g_f 2 ∈
      Submodule.span F ({k328r8g_f 2} : Set (Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F)) :=
    Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton _))
  exact Submodule.mem_sup.mpr ⟨_, hw', _, hspan, sub_add_cancel _ _⟩

private def k328r8g_perpE2 {F : Type} [Field F] (b c : F) :
    Submodule F (Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F) where
  carrier := {x | polar (k328r8g_Q b c) (k328r8g_e 2) x = 0}
  add_mem' := by
    intro x y hx hy
    simp only [Set.mem_setOf_eq] at hx hy ⊢
    rw [polar_add_right, hx, hy, add_zero]
  zero_mem' := by simp only [Set.mem_setOf_eq, polar_zero_right]
  smul_mem' := by
    intro a x hx
    simp only [Set.mem_setOf_eq] at hx ⊢
    rw [polar_smul_right_eq, hx, mul_zero]

private def k328r8g_perpF2 {F : Type} [Field F] (b c : F) :
    Submodule F (Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F) where
  carrier := {x | polar (k328r8g_Q b c) (k328r8g_f 2) x = 0}
  add_mem' := by
    intro x y hx hy
    simp only [Set.mem_setOf_eq] at hx hy ⊢
    rw [polar_add_right, hx, hy, add_zero]
  zero_mem' := by simp only [Set.mem_setOf_eq, polar_zero_right]
  smul_mem' := by
    intro a x hx
    simp only [Set.mem_setOf_eq] at hx ⊢
    rw [polar_smul_right_eq, hx, mul_zero]

private theorem k328r8g_A1_le_perpE2 {F : Type} [Field F] (b c : F) :
    k328r8g_A1 b c ≤ k328r8g_perpE2 b c := by
  rw [k328r8g_A1, Submodule.span_le]
  rintro x (rfl | rfl)
  · change polar (k328r8g_Q b c) (k328r8g_e 2) (k328r8g_a11 : Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F) = 0
    rw [k328r8g_polar_e2_apply]; simp [k328r8g_a11, k328r8g_e, k328r8g_f]
  · change polar (k328r8g_Q b c) (k328r8g_e 2) (k328r8g_a12 : Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F) = 0
    rw [k328r8g_polar_e2_apply]; simp [k328r8g_a12, k328r8g_e, k328r8g_f]

private theorem k328r8g_A2_le_perpE2 {F : Type} [Field F] (b c : F) :
    k328r8g_A2 b c ≤ k328r8g_perpE2 b c := by
  rw [k328r8g_A2, Submodule.span_le]
  rintro x (rfl | rfl)
  · change polar (k328r8g_Q b c) (k328r8g_e 2) (k328r8g_a21 : Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F) = 0
    rw [k328r8g_polar_e2_apply]; simp [k328r8g_a21, k328r8g_e, k328r8g_f]
  · change polar (k328r8g_Q b c) (k328r8g_e 2) (k328r8g_a22 : Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F) = 0
    rw [k328r8g_polar_e2_apply]; simp [k328r8g_a22, k328r8g_e, k328r8g_f]

private theorem k328r8g_A3_le_perpE2 {F : Type} [Field F] (b c : F) :
    k328r8g_A3 b c ≤ k328r8g_perpE2 b c := by
  rw [k328r8g_A3, Submodule.span_le]
  rintro x (rfl | rfl)
  · change polar (k328r8g_Q b c) (k328r8g_e 2) (k328r8g_u : Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F) = 0
    rw [k328r8g_polar_e2_apply]; simp
  · change polar (k328r8g_Q b c) (k328r8g_e 2) (k328r8g_v : Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F) = 0
    rw [k328r8g_polar_e2_apply]; simp

private theorem k328r8g_A1_le_perpF2 {F : Type} [Field F] (b c : F) :
    k328r8g_A1 b c ≤ k328r8g_perpF2 b c := by
  rw [k328r8g_A1, Submodule.span_le]
  rintro x (rfl | rfl)
  · change polar (k328r8g_Q b c) (k328r8g_f 2) (k328r8g_a11 : Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F) = 0
    rw [k328r8g_polar_f2_apply]; simp [k328r8g_a11, k328r8g_e, k328r8g_f]
  · change polar (k328r8g_Q b c) (k328r8g_f 2) (k328r8g_a12 : Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F) = 0
    rw [k328r8g_polar_f2_apply]; simp [k328r8g_a12, k328r8g_e, k328r8g_f]

private theorem k328r8g_A2_le_perpF2 {F : Type} [Field F] (b c : F) :
    k328r8g_A2 b c ≤ k328r8g_perpF2 b c := by
  rw [k328r8g_A2, Submodule.span_le]
  rintro x (rfl | rfl)
  · change polar (k328r8g_Q b c) (k328r8g_f 2) (k328r8g_a21 : Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F) = 0
    rw [k328r8g_polar_f2_apply]; simp [k328r8g_a21, k328r8g_e, k328r8g_f]
  · change polar (k328r8g_Q b c) (k328r8g_f 2) (k328r8g_a22 : Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F) = 0
    rw [k328r8g_polar_f2_apply]; simp [k328r8g_a22, k328r8g_e, k328r8g_f]

private theorem k328r8g_A3_le_perpF2 {F : Type} [Field F] (b c : F) :
    k328r8g_A3 b c ≤ k328r8g_perpF2 b c := by
  rw [k328r8g_A3, Submodule.span_le]
  rintro x (rfl | rfl)
  · change polar (k328r8g_Q b c) (k328r8g_f 2) (k328r8g_u : Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F) = 0
    rw [k328r8g_polar_f2_apply]; simp
  · change polar (k328r8g_Q b c) (k328r8g_f 2) (k328r8g_v : Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F) = 0
    rw [k328r8g_polar_f2_apply]; simp

private theorem k328r8g_H_eq {F : Type} [Field F] [Fintype F] [CharP F 2] (b c : F)
    (hbc : ∀ s : F, s ^ 2 + b * s + c ≠ 0) :
    StatedOmega (StatedQuadMinus 4 F b c) =
      (elementaryGroup (k328r8g_Q b c)).map
        (toLinEquiv (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F).symm.toMonoidHom :=
  statedOmega_quadMinus_eq_map (n := 4) (by norm_num) hbc

private theorem k328r8g_mem_cent {F : Type} [Field F] [Fintype F] [CharP F 2] (b c : F)
    (hbc : ∀ s : F, s ^ 2 + b * s + c ≠ 0) {s : GL (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F}
    (hs : ∀ w, k328r8g_Q b c ((s : Matrix (Fin 3 ⊕ Fin 3 ⊕ Fin 2) (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F) *ᵥ w) =
      k328r8g_Q b c w)
    {x w : Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F}
    (hx : (s : Matrix (Fin 3 ⊕ Fin 3 ⊕ Fin 2) (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F) *ᵥ x = x)
    (hw : (s : Matrix (Fin 3 ⊕ Fin 3 ⊕ Fin 2) (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F) *ᵥ w = w) :
    (toLinEquiv (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F).symm (eichler (k328r8g_Q b c) x w) ∈
      StatedOmega (StatedQuadMinus 4 F b c) ⊓ Subgroup.centralizer {s} := by
  refine ⟨?_, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
  · rw [k328r8g_H_eq b c hbc]
    exact ⟨_, eichler_mem_elementaryGroup _ x w, rfl⟩
  · apply (toLinEquiv (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F).injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
    have hsO : toLinEquiv (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F s ∈
        TauCeti.QuadraticMap.orthogonalGroup (k328r8g_Q b c) :=
      TauCeti.QuadraticMap.mem_orthogonalGroup_iff.2 fun w => hs w
    have h := eichler_conj hsO x w
    rw [toLinEquiv_apply, toLinEquiv_apply, hx, hw, mul_inv_eq_iff_eq_mul] at h
    exact h.symm

private theorem k328r8g_Q_e2 {F : Type} [Field F] (b c : F) :
    k328r8g_Q b c (k328r8g_e 2) = 0 := by
  rw [quadMinus_apply]; simp [k328r8g_e, Pi.single_apply]

private theorem k328r8g_Q_f2 {F : Type} [Field F] (b c : F) :
    k328r8g_Q b c (k328r8g_f 2) = 0 := by
  rw [quadMinus_apply]; simp [k328r8g_f, Pi.single_apply]

private theorem k328r8g_Q_u {F : Type} [Field F] (b c : F) :
    k328r8g_Q b c (k328r8g_u : Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F) = 1 := by
  rw [quadMinus_apply]; simp [k328r8g_u]

private theorem k328r8g_polar_e2_f2 {F : Type} [Field F] (b c : F) :
    polar (k328r8g_Q b c) (k328r8g_e 2) (k328r8g_f 2) = 1 := by
  rw [k328r8g_polar_e2_apply]; simp [k328r8g_f]

private theorem k328r8g_polar_e2_u {F : Type} [Field F] (b c : F) :
    polar (k328r8g_Q b c) (k328r8g_e 2) (k328r8g_u : Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F) = 0 := by
  rw [k328r8g_polar_e2_apply]; simp [k328r8g_u]

private theorem k328r8g_polar_f2_u {F : Type} [Field F] (b c : F) :
    polar (k328r8g_Q b c) (k328r8g_f 2) (k328r8g_u : Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F) = 0 := by
  rw [k328r8g_polar_f2_apply]; simp [k328r8g_u]

private theorem k328r8g_eichler_JJ_e2_mem {F : Type} [Field F] [CharP F 2] (b c : F)
    {Y : Subgroup ((Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F) ≃ₗ[F] (Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F))}
    (h1 : ∀ a ∈ k328r8g_A1 b c, eichler (k328r8g_Q b c) (k328r8g_e 2) a ∈ Y)
    (h2 : ∀ a ∈ k328r8g_A2 b c, eichler (k328r8g_Q b c) (k328r8g_e 2) a ∈ Y)
    (h3 : ∀ a ∈ k328r8g_A3 b c, eichler (k328r8g_Q b c) (k328r8g_e 2) a ∈ Y) :
    ∀ j ∈ k328r8g_JJ b c, eichler (k328r8g_Q b c) (k328r8g_e 2) j ∈ Y := by
  intro j hj
  rw [k328r8g_JJ] at hj
  obtain ⟨j12, hj12, a3, ha3, hj_eq⟩ := Submodule.mem_sup.mp hj
  rw [Submodule.mem_sup] at hj12
  obtain ⟨a1, ha1, a2, ha2, hj12_eq⟩ := hj12
  have hp1 : polar (k328r8g_Q b c) (k328r8g_e 2) a1 = 0 := k328r8g_A1_le_perpE2 b c ha1
  have hp2 : polar (k328r8g_Q b c) (k328r8g_e 2) a2 = 0 := k328r8g_A2_le_perpE2 b c ha2
  have hp3 : polar (k328r8g_Q b c) (k328r8g_e 2) a3 = 0 := k328r8g_A3_le_perpE2 b c ha3
  have hp12 : polar (k328r8g_Q b c) (k328r8g_e 2) (a1 + a2) = 0 := by
    rw [polar_add_right, hp1, hp2, add_zero]
  rw [← hj_eq, ← hj12_eq, ← eichler_mul hp12 hp3, ← eichler_mul hp1 hp2]
  exact Y.mul_mem (Y.mul_mem (h1 a1 ha1) (h2 a2 ha2)) (h3 a3 ha3)

private theorem k328r8g_eichler_JJ_f2_mem {F : Type} [Field F] [CharP F 2] (b c : F)
    {Y : Subgroup ((Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F) ≃ₗ[F] (Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F))}
    (h1 : ∀ a ∈ k328r8g_A1 b c, eichler (k328r8g_Q b c) (k328r8g_f 2) a ∈ Y)
    (h2 : ∀ a ∈ k328r8g_A2 b c, eichler (k328r8g_Q b c) (k328r8g_f 2) a ∈ Y)
    (h3 : ∀ a ∈ k328r8g_A3 b c, eichler (k328r8g_Q b c) (k328r8g_f 2) a ∈ Y) :
    ∀ j ∈ k328r8g_JJ b c, eichler (k328r8g_Q b c) (k328r8g_f 2) j ∈ Y := by
  intro j hj
  rw [k328r8g_JJ] at hj
  obtain ⟨j12, hj12, a3, ha3, hj_eq⟩ := Submodule.mem_sup.mp hj
  rw [Submodule.mem_sup] at hj12
  obtain ⟨a1, ha1, a2, ha2, hj12_eq⟩ := hj12
  have hp1 : polar (k328r8g_Q b c) (k328r8g_f 2) a1 = 0 := k328r8g_A1_le_perpF2 b c ha1
  have hp2 : polar (k328r8g_Q b c) (k328r8g_f 2) a2 = 0 := k328r8g_A2_le_perpF2 b c ha2
  have hp3 : polar (k328r8g_Q b c) (k328r8g_f 2) a3 = 0 := k328r8g_A3_le_perpF2 b c ha3
  have hp12 : polar (k328r8g_Q b c) (k328r8g_f 2) (a1 + a2) = 0 := by
    rw [polar_add_right, hp1, hp2, add_zero]
  rw [← hj_eq, ← hj12_eq, ← eichler_mul hp12 hp3, ← eichler_mul hp1 hp2]
  exact Y.mul_mem (Y.mul_mem (h1 a1 ha1) (h2 a2 ha2)) (h3 a3 ha3)

private theorem k328r8g_rootGroup_e2_le {F : Type} [Field F] [CharP F 2] (b c : F)
    {Y : Subgroup ((Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F) ≃ₗ[F] (Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F))}
    (h1 : ∀ a ∈ k328r8g_A1 b c, eichler (k328r8g_Q b c) (k328r8g_e 2) a ∈ Y)
    (h2 : ∀ a ∈ k328r8g_A2 b c, eichler (k328r8g_Q b c) (k328r8g_e 2) a ∈ Y)
    (h3 : ∀ a ∈ k328r8g_A3 b c, eichler (k328r8g_Q b c) (k328r8g_e 2) a ∈ Y) :
    rootGroup (k328r8g_Q b c) (k328r8g_e 2) ≤ Y := by
  intro g hg
  obtain ⟨w, hw, rfl⟩ := mem_rootGroup.mp hg
  obtain ⟨j, hj, z, hz, hjeq⟩ := Submodule.mem_sup.mp (k328r8g_perp_e2_le b c hw)
  obtain ⟨cc, hcc⟩ := Submodule.mem_span_singleton.mp hz
  rw [← hjeq, ← hcc, eichler_add_smul_self (k328r8g_Q_e2 b c)]
  exact k328r8g_eichler_JJ_e2_mem b c h1 h2 h3 j hj

private theorem k328r8g_rootGroup_f2_le {F : Type} [Field F] [CharP F 2] (b c : F)
    {Y : Subgroup ((Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F) ≃ₗ[F] (Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F))}
    (h1 : ∀ a ∈ k328r8g_A1 b c, eichler (k328r8g_Q b c) (k328r8g_f 2) a ∈ Y)
    (h2 : ∀ a ∈ k328r8g_A2 b c, eichler (k328r8g_Q b c) (k328r8g_f 2) a ∈ Y)
    (h3 : ∀ a ∈ k328r8g_A3 b c, eichler (k328r8g_Q b c) (k328r8g_f 2) a ∈ Y) :
    rootGroup (k328r8g_Q b c) (k328r8g_f 2) ≤ Y := by
  intro g hg
  obtain ⟨w, hw, rfl⟩ := mem_rootGroup.mp hg
  obtain ⟨j, hj, z, hz, hjeq⟩ := Submodule.mem_sup.mp (k328r8g_perp_f2_le b c hw)
  obtain ⟨cc, hcc⟩ := Submodule.mem_span_singleton.mp hz
  rw [← hjeq, ← hcc, eichler_add_smul_self (k328r8g_Q_f2 b c)]
  exact k328r8g_eichler_JJ_f2_mem b c h1 h2 h3 j hj

private theorem k328r8g_gen_le {F : Type} [Field F] [Fintype F] [DecidableEq F] [CharP F 2]
    (b c : F) (hbc : ∀ s : F, s ^ 2 + b * s + c ≠ 0)
    {J : Subgroup (GL (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F)}
    {s1 s2 s3 : GL (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F}
    (h1 : StatedOmega (StatedQuadMinus 4 F b c) ⊓ Subgroup.centralizer {s1} ≤ J)
    (h2 : StatedOmega (StatedQuadMinus 4 F b c) ⊓ Subgroup.centralizer {s2} ≤ J)
    (h3 : StatedOmega (StatedQuadMinus 4 F b c) ⊓ Subgroup.centralizer {s3} ≤ J)
    (i1 : ∀ w, k328r8g_Q b c
      ((s1 : Matrix (Fin 3 ⊕ Fin 3 ⊕ Fin 2) (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F) *ᵥ w) =
        k328r8g_Q b c w)
    (i2 : ∀ w, k328r8g_Q b c
      ((s2 : Matrix (Fin 3 ⊕ Fin 3 ⊕ Fin 2) (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F) *ᵥ w) =
        k328r8g_Q b c w)
    (i3 : ∀ w, k328r8g_Q b c
      ((s3 : Matrix (Fin 3 ⊕ Fin 3 ⊕ Fin 2) (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F) *ᵥ w) =
        k328r8g_Q b c w)
    (he1 : (s1 : Matrix (Fin 3 ⊕ Fin 3 ⊕ Fin 2) (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F) *ᵥ
      (k328r8g_e 2 : Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F) = k328r8g_e 2)
    (hf1 : (s1 : Matrix (Fin 3 ⊕ Fin 3 ⊕ Fin 2) (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F) *ᵥ
      (k328r8g_f 2 : Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F) = k328r8g_f 2)
    (he2 : (s2 : Matrix (Fin 3 ⊕ Fin 3 ⊕ Fin 2) (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F) *ᵥ
      (k328r8g_e 2 : Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F) = k328r8g_e 2)
    (hf2 : (s2 : Matrix (Fin 3 ⊕ Fin 3 ⊕ Fin 2) (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F) *ᵥ
      (k328r8g_f 2 : Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F) = k328r8g_f 2)
    (he3 : (s3 : Matrix (Fin 3 ⊕ Fin 3 ⊕ Fin 2) (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F) *ᵥ
      (k328r8g_e 2 : Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F) = k328r8g_e 2)
    (hf3 : (s3 : Matrix (Fin 3 ⊕ Fin 3 ⊕ Fin 2) (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F) *ᵥ
      (k328r8g_f 2 : Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F) = k328r8g_f 2)
    (fA1 : ∀ a ∈ k328r8g_A1 b c,
      (s1 : Matrix (Fin 3 ⊕ Fin 3 ⊕ Fin 2) (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F) *ᵥ a = a)
    (fA2 : ∀ a ∈ k328r8g_A2 b c,
      (s2 : Matrix (Fin 3 ⊕ Fin 3 ⊕ Fin 2) (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F) *ᵥ a = a)
    (fA3 : ∀ a ∈ k328r8g_A3 b c,
      (s3 : Matrix (Fin 3 ⊕ Fin 3 ⊕ Fin 2) (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F) *ᵥ a = a) :
    StatedOmega (StatedQuadMinus 4 F b c) ≤ J := by
  set Y : Subgroup ((Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F) ≃ₗ[F] (Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F)) :=
    J.comap (toLinEquiv (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F).symm.toMonoidHom with hY
  have mem1 : ∀ x w, (s1 : Matrix (Fin 3 ⊕ Fin 3 ⊕ Fin 2) (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F) *ᵥ x = x →
      (s1 : Matrix (Fin 3 ⊕ Fin 3 ⊕ Fin 2) (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F) *ᵥ w = w →
        eichler (k328r8g_Q b c) x w ∈ Y := fun x w hx hw =>
    h1 (k328r8g_mem_cent b c hbc i1 hx hw)
  have mem2 : ∀ x w, (s2 : Matrix (Fin 3 ⊕ Fin 3 ⊕ Fin 2) (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F) *ᵥ x = x →
      (s2 : Matrix (Fin 3 ⊕ Fin 3 ⊕ Fin 2) (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F) *ᵥ w = w →
        eichler (k328r8g_Q b c) x w ∈ Y := fun x w hx hw =>
    h2 (k328r8g_mem_cent b c hbc i2 hx hw)
  have mem3 : ∀ x w, (s3 : Matrix (Fin 3 ⊕ Fin 3 ⊕ Fin 2) (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F) *ᵥ x = x →
      (s3 : Matrix (Fin 3 ⊕ Fin 3 ⊕ Fin 2) (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F) *ᵥ w = w →
        eichler (k328r8g_Q b c) x w ∈ Y := fun x w hx hw =>
    h3 (k328r8g_mem_cent b c hbc i3 hx hw)
  have hA1e : ∀ a ∈ k328r8g_A1 b c, eichler (k328r8g_Q b c) (k328r8g_e 2) a ∈ Y :=
    fun a ha => mem1 _ _ he1 (fA1 a ha)
  have hA2e : ∀ a ∈ k328r8g_A2 b c, eichler (k328r8g_Q b c) (k328r8g_e 2) a ∈ Y :=
    fun a ha => mem2 _ _ he2 (fA2 a ha)
  have hA3e : ∀ a ∈ k328r8g_A3 b c, eichler (k328r8g_Q b c) (k328r8g_e 2) a ∈ Y :=
    fun a ha => mem3 _ _ he3 (fA3 a ha)
  have hA1f : ∀ a ∈ k328r8g_A1 b c, eichler (k328r8g_Q b c) (k328r8g_f 2) a ∈ Y :=
    fun a ha => mem1 _ _ hf1 (fA1 a ha)
  have hA2f : ∀ a ∈ k328r8g_A2 b c, eichler (k328r8g_Q b c) (k328r8g_f 2) a ∈ Y :=
    fun a ha => mem2 _ _ hf2 (fA2 a ha)
  have hA3f : ∀ a ∈ k328r8g_A3 b c, eichler (k328r8g_Q b c) (k328r8g_f 2) a ∈ Y :=
    fun a ha => mem3 _ _ hf3 (fA3 a ha)
  have hroot_e : rootGroup (k328r8g_Q b c) (k328r8g_e 2) ≤ Y :=
    k328r8g_rootGroup_e2_le b c hA1e hA2e hA3e
  have hroot_f : rootGroup (k328r8g_Q b c) (k328r8g_f 2) ≤ Y :=
    k328r8g_rootGroup_f2_le b c hA1f hA2f hA3f
  have hnd : ∀ x : Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F,
      (∀ y, polar (k328r8g_Q b c) x y = 0) → x = 0 := fun x hx =>
    (CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_quadMinus_of_finite 4 F hbc).1 x
      fun y => hx y
  have hE : elementaryGroup (k328r8g_Q b c) ≤ Y :=
    (CFSG.ClassicalGroups.Orthogonal.OmegaSiegel.elementaryGroup_le_rootGroup_sup hnd (k328r8g_Q_e2 b c) (k328r8g_Q_f2 b c)
      (k328r8g_polar_e2_f2 b c) (k328r8g_polar_e2_u b c) (k328r8g_polar_f2_u b c)
      (k328r8g_Q_u b c)).trans (sup_le hroot_e hroot_f)
  intro g hg
  rw [k328r8g_H_eq b c hbc] at hg
  obtain ⟨y, hy, rfl⟩ := hg
  exact hE hy

private def k328r8g_fixed {F : Type} [Field F]
    (s : Matrix (Fin 3 ⊕ Fin 3 ⊕ Fin 2) (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F) :
    Submodule F (Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F) where
  carrier := {x | s *ᵥ x = x}
  add_mem' := by
    intro x y hx hy
    simp only [Set.mem_setOf_eq] at hx hy ⊢
    rw [Matrix.mulVec_add, hx, hy]
  zero_mem' := by simp only [Set.mem_setOf_eq]; exact Matrix.mulVec_zero s
  smul_mem' := by
    intro a x hx
    simp only [Set.mem_setOf_eq] at hx ⊢
    rw [Matrix.mulVec_smul, hx]

private theorem k328r8g_t0_fix_e2 {F : Type} [Field F] [Fintype F] [DecidableEq F] (_b _c : F)
    (t₀ : GL (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F)
    (ht : (t₀ : Matrix _ _ F) = ofColumns F k328r8g_tc) :
    (t₀ : Matrix _ _ F) *ᵥ (k328r8g_e 2 : Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F) = k328r8g_e 2 := by
  rw [ht, k328r8g_ofColumns_mulVec_single]; rfl

private theorem k328r8g_t0_fix_f2 {F : Type} [Field F] [Fintype F] [DecidableEq F] (_b _c : F)
    (t₀ : GL (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F)
    (ht : (t₀ : Matrix _ _ F) = ofColumns F k328r8g_tc) :
    (t₀ : Matrix _ _ F) *ᵥ (k328r8g_f 2 : Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F) = k328r8g_f 2 := by
  rw [ht, k328r8g_ofColumns_mulVec_single]; rfl

private theorem k328r8g_t0_fix_u {F : Type} [Field F] [Fintype F] [DecidableEq F] (_b _c : F)
    (t₀ : GL (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F)
    (ht : (t₀ : Matrix _ _ F) = ofColumns F k328r8g_tc) :
    (t₀ : Matrix _ _ F) *ᵥ (k328r8g_u : Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F) = k328r8g_u := by
  rw [ht, k328r8g_ofColumns_mulVec_single]; rfl

private theorem k328r8g_t0_fix_v {F : Type} [Field F] [Fintype F] [DecidableEq F] (_b _c : F)
    (t₀ : GL (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F)
    (ht : (t₀ : Matrix _ _ F) = ofColumns F k328r8g_tc) :
    (t₀ : Matrix _ _ F) *ᵥ (k328r8g_v : Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F) = k328r8g_v := by
  rw [ht, k328r8g_ofColumns_mulVec_single]; rfl

private theorem k328r8g_t0_fix_A3 {F : Type} [Field F] [Fintype F] [DecidableEq F] (b c : F)
    (t₀ : GL (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F)
    (ht : (t₀ : Matrix _ _ F) = ofColumns F k328r8g_tc) :
    k328r8g_A3 b c ≤ k328r8g_fixed (t₀ : Matrix _ _ F) := by
  rw [k328r8g_A3, Submodule.span_le]
  rintro x (rfl | rfl)
  · exact k328r8g_t0_fix_u b c t₀ ht
  · exact k328r8g_t0_fix_v b c t₀ ht

private theorem k328r8g_z0_fix_e2 {F : Type} [Field F] [Fintype F] [DecidableEq F] (b c α : F)
    (z₀ : GL (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F)
    (hz : (z₀ : Matrix _ _ F) = ofColumns F (k328r8g_zc b c α)) :
    (z₀ : Matrix _ _ F) *ᵥ (k328r8g_e 2 : Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F) = k328r8g_e 2 := by
  rw [hz, k328r8g_ofColumns_mulVec_single]; rfl

private theorem k328r8g_z0_fix_f2 {F : Type} [Field F] [Fintype F] [DecidableEq F] (b c α : F)
    (z₀ : GL (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F)
    (hz : (z₀ : Matrix _ _ F) = ofColumns F (k328r8g_zc b c α)) :
    (z₀ : Matrix _ _ F) *ᵥ (k328r8g_f 2 : Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F) = k328r8g_f 2 := by
  rw [hz, k328r8g_ofColumns_mulVec_single]; rfl


private theorem k328r8g_s1_fix_a11 {F : Type} [Field F] [Fintype F] [DecidableEq F] [CharP F 2] (b c α : F)
    (z₀ t₀ : GL (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F)
    (hz : (z₀ : Matrix _ _ F) = ofColumns F (k328r8g_zc b c α))
    (ht : (t₀ : Matrix _ _ F) = ofColumns F k328r8g_tc) :
    ((z₀ * t₀ ^ 2 : GL (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F) : Matrix _ _ F) *ᵥ
      (k328r8g_a11 : Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F) = k328r8g_a11 := by
  rw [Units.val_mul, Units.val_pow_eq_pow_val, pow_two, ← Matrix.mulVec_mulVec,
    ← Matrix.mulVec_mulVec, hz, ht]
  funext k
  rcases k with i | i | j
  · fin_cases i <;> simp [ofColumns, Matrix.mulVec, dotProduct, k328r8g_a11, k328r8g_zc, k328r8g_tc,
      k328r8g_e, k328r8g_f, k328r8g_u, k328r8g_v, Pi.single_apply, Fintype.sum_sum_type,
      Fin.sum_univ_three, CharTwo.add_self_eq_zero]
  · fin_cases i <;> simp [ofColumns, Matrix.mulVec, dotProduct, k328r8g_a11, k328r8g_zc, k328r8g_tc,
      k328r8g_e, k328r8g_f, k328r8g_u, k328r8g_v, Pi.single_apply, Fintype.sum_sum_type,
      Fin.sum_univ_three, CharTwo.add_self_eq_zero]
  · fin_cases j <;> simp [ofColumns, Matrix.mulVec, dotProduct, k328r8g_a11, k328r8g_zc, k328r8g_tc,
      k328r8g_e, k328r8g_f, k328r8g_u, k328r8g_v, Pi.single_apply, Fintype.sum_sum_type,
      Fin.sum_univ_three, CharTwo.add_self_eq_zero]

private theorem k328r8g_s1_fix_a12 {F : Type} [Field F] [Fintype F] [DecidableEq F] [CharP F 2] (b c α : F)
    (z₀ t₀ : GL (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F)
    (hz : (z₀ : Matrix _ _ F) = ofColumns F (k328r8g_zc b c α))
    (ht : (t₀ : Matrix _ _ F) = ofColumns F k328r8g_tc) :
    ((z₀ * t₀ ^ 2 : GL (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F) : Matrix _ _ F) *ᵥ
      (k328r8g_a12 : Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F) = k328r8g_a12 := by
  rw [Units.val_mul, Units.val_pow_eq_pow_val, pow_two, ← Matrix.mulVec_mulVec,
    ← Matrix.mulVec_mulVec, hz, ht]
  funext k
  rcases k with i | i | j
  · fin_cases i <;> simp [ofColumns, Matrix.mulVec, dotProduct, k328r8g_a12, k328r8g_zc, k328r8g_tc,
      k328r8g_e, k328r8g_f, k328r8g_u, k328r8g_v, Pi.single_apply, Fintype.sum_sum_type,
      Fin.sum_univ_three, CharTwo.add_self_eq_zero]
  · fin_cases i <;> simp [ofColumns, Matrix.mulVec, dotProduct, k328r8g_a12, k328r8g_zc, k328r8g_tc,
      k328r8g_e, k328r8g_f, k328r8g_u, k328r8g_v, Pi.single_apply, Fintype.sum_sum_type,
      Fin.sum_univ_three, CharTwo.add_self_eq_zero]
  · fin_cases j <;> simp [ofColumns, Matrix.mulVec, dotProduct, k328r8g_a12, k328r8g_zc, k328r8g_tc,
      k328r8g_e, k328r8g_f, k328r8g_u, k328r8g_v, Pi.single_apply, Fintype.sum_sum_type,
      Fin.sum_univ_three, CharTwo.add_self_eq_zero]

private theorem k328r8g_s2_fix_a21 {F : Type} [Field F] [Fintype F] [DecidableEq F] [CharP F 2] (b c α : F)
    (z₀ t₀ : GL (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F)
    (hz : (z₀ : Matrix _ _ F) = ofColumns F (k328r8g_zc b c α))
    (ht : (t₀ : Matrix _ _ F) = ofColumns F k328r8g_tc) :
    ((z₀ * t₀ : GL (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F) : Matrix _ _ F) *ᵥ
      (k328r8g_a21 : Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F) = k328r8g_a21 := by
  rw [Units.val_mul, ← Matrix.mulVec_mulVec, hz, ht]
  funext k
  rcases k with i | i | j
  · fin_cases i <;> simp [ofColumns, Matrix.mulVec, dotProduct, k328r8g_a21, k328r8g_zc, k328r8g_tc,
      k328r8g_e, k328r8g_f, k328r8g_u, k328r8g_v, Pi.single_apply, Fintype.sum_sum_type,
      Fin.sum_univ_three, CharTwo.add_self_eq_zero]
  · fin_cases i <;> simp [ofColumns, Matrix.mulVec, dotProduct, k328r8g_a21, k328r8g_zc, k328r8g_tc,
      k328r8g_e, k328r8g_f, k328r8g_u, k328r8g_v, Pi.single_apply, Fintype.sum_sum_type,
      Fin.sum_univ_three, CharTwo.add_self_eq_zero]
  · fin_cases j <;> simp [ofColumns, Matrix.mulVec, dotProduct, k328r8g_a21, k328r8g_zc, k328r8g_tc,
      k328r8g_e, k328r8g_f, k328r8g_u, k328r8g_v, Pi.single_apply, Fintype.sum_sum_type,
      Fin.sum_univ_three, CharTwo.add_self_eq_zero]

private theorem k328r8g_s2_fix_a22 {F : Type} [Field F] [Fintype F] [DecidableEq F] [CharP F 2] (b c α : F)
    (z₀ t₀ : GL (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F)
    (hz : (z₀ : Matrix _ _ F) = ofColumns F (k328r8g_zc b c α))
    (ht : (t₀ : Matrix _ _ F) = ofColumns F k328r8g_tc) :
    ((z₀ * t₀ : GL (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F) : Matrix _ _ F) *ᵥ
      (k328r8g_a22 : Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F) = k328r8g_a22 := by
  rw [Units.val_mul, ← Matrix.mulVec_mulVec, hz, ht]
  funext k
  rcases k with i | i | j
  · fin_cases i <;> simp [ofColumns, Matrix.mulVec, dotProduct, k328r8g_a22, k328r8g_zc, k328r8g_tc,
      k328r8g_e, k328r8g_f, k328r8g_u, k328r8g_v, Pi.single_apply, Fintype.sum_sum_type,
      Fin.sum_univ_three, CharTwo.add_self_eq_zero]
  · fin_cases i <;> simp [ofColumns, Matrix.mulVec, dotProduct, k328r8g_a22, k328r8g_zc, k328r8g_tc,
      k328r8g_e, k328r8g_f, k328r8g_u, k328r8g_v, Pi.single_apply, Fintype.sum_sum_type,
      Fin.sum_univ_three, CharTwo.add_self_eq_zero]
  · fin_cases j <;> simp [ofColumns, Matrix.mulVec, dotProduct, k328r8g_a22, k328r8g_zc, k328r8g_tc,
      k328r8g_e, k328r8g_f, k328r8g_u, k328r8g_v, Pi.single_apply, Fintype.sum_sum_type,
      Fin.sum_univ_three, CharTwo.add_self_eq_zero]

private theorem k328r8g_s1_fix_A1 {F : Type} [Field F] [Fintype F] [DecidableEq F] [CharP F 2] (b c α : F)
    (z₀ t₀ : GL (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F)
    (hz : (z₀ : Matrix _ _ F) = ofColumns F (k328r8g_zc b c α))
    (ht : (t₀ : Matrix _ _ F) = ofColumns F k328r8g_tc) :
    k328r8g_A1 b c ≤ k328r8g_fixed
      (((z₀ * t₀ ^ 2 : GL (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F) : Matrix _ _ F)) := by
  rw [k328r8g_A1, Submodule.span_le]
  rintro x (rfl | rfl)
  · exact k328r8g_s1_fix_a11 b c α z₀ t₀ hz ht
  · exact k328r8g_s1_fix_a12 b c α z₀ t₀ hz ht

private theorem k328r8g_s2_fix_A2 {F : Type} [Field F] [Fintype F] [DecidableEq F] [CharP F 2] (b c α : F)
    (z₀ t₀ : GL (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F)
    (hz : (z₀ : Matrix _ _ F) = ofColumns F (k328r8g_zc b c α))
    (ht : (t₀ : Matrix _ _ F) = ofColumns F k328r8g_tc) :
    k328r8g_A2 b c ≤ k328r8g_fixed
      (((z₀ * t₀ : GL (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F) : Matrix _ _ F)) := by
  rw [k328r8g_A2, Submodule.span_le]
  rintro x (rfl | rfl)
  · exact k328r8g_s2_fix_a21 b c α z₀ t₀ hz ht
  · exact k328r8g_s2_fix_a22 b c α z₀ t₀ hz ht

private theorem k328r8g_s1_fix_e2 {F : Type} [Field F] [Fintype F] [DecidableEq F] (b c α : F)
    (z₀ t₀ : GL (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F)
    (hz : (z₀ : Matrix _ _ F) = ofColumns F (k328r8g_zc b c α))
    (ht : (t₀ : Matrix _ _ F) = ofColumns F k328r8g_tc) :
    (((z₀ * t₀ ^ 2 : GL (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F)) : Matrix _ _ F) *ᵥ
      (k328r8g_e 2 : Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F) = k328r8g_e 2 := by
  rw [Units.val_mul, Units.val_pow_eq_pow_val, pow_two, ← Matrix.mulVec_mulVec,
    ← Matrix.mulVec_mulVec, k328r8g_t0_fix_e2 b c t₀ ht, k328r8g_t0_fix_e2 b c t₀ ht,
    k328r8g_z0_fix_e2 b c α z₀ hz]

private theorem k328r8g_s1_fix_f2 {F : Type} [Field F] [Fintype F] [DecidableEq F] (b c α : F)
    (z₀ t₀ : GL (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F)
    (hz : (z₀ : Matrix _ _ F) = ofColumns F (k328r8g_zc b c α))
    (ht : (t₀ : Matrix _ _ F) = ofColumns F k328r8g_tc) :
    (((z₀ * t₀ ^ 2 : GL (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F)) : Matrix _ _ F) *ᵥ
      (k328r8g_f 2 : Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F) = k328r8g_f 2 := by
  rw [Units.val_mul, Units.val_pow_eq_pow_val, pow_two, ← Matrix.mulVec_mulVec,
    ← Matrix.mulVec_mulVec, k328r8g_t0_fix_f2 b c t₀ ht, k328r8g_t0_fix_f2 b c t₀ ht,
    k328r8g_z0_fix_f2 b c α z₀ hz]

private theorem k328r8g_s2_fix_e2 {F : Type} [Field F] [Fintype F] [DecidableEq F] (b c α : F)
    (z₀ t₀ : GL (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F)
    (hz : (z₀ : Matrix _ _ F) = ofColumns F (k328r8g_zc b c α))
    (ht : (t₀ : Matrix _ _ F) = ofColumns F k328r8g_tc) :
    (((z₀ * t₀ : GL (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F)) : Matrix _ _ F) *ᵥ
      (k328r8g_e 2 : Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F) = k328r8g_e 2 := by
  rw [Units.val_mul, ← Matrix.mulVec_mulVec, k328r8g_t0_fix_e2 b c t₀ ht,
    k328r8g_z0_fix_e2 b c α z₀ hz]

private theorem k328r8g_s2_fix_f2 {F : Type} [Field F] [Fintype F] [DecidableEq F] (b c α : F)
    (z₀ t₀ : GL (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F)
    (hz : (z₀ : Matrix _ _ F) = ofColumns F (k328r8g_zc b c α))
    (ht : (t₀ : Matrix _ _ F) = ofColumns F k328r8g_tc) :
    (((z₀ * t₀ : GL (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F)) : Matrix _ _ F) *ᵥ
      (k328r8g_f 2 : Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F) = k328r8g_f 2 := by
  rw [Units.val_mul, ← Matrix.mulVec_mulVec, k328r8g_t0_fix_f2 b c t₀ ht,
    k328r8g_z0_fix_f2 b c α z₀ hz]


theorem row8_gen (F : Type) [Field F] [Fintype F] [DecidableEq F]
    (hF : Fintype.card F = 8) (b c : F)
    (hbc : ∀ s : F, s ^ 2 + b * s + c ≠ 0) (α : F) (hα : α ^ 2 + α = 1 + c / b ^ 2) :
    let e : Fin 3 → (Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F) := fun i => bv F (Sum.inl i)
    let f : Fin 3 → (Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F) := fun i => bv F (Sum.inr (Sum.inl i))
    let u : Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F := bv F (Sum.inr (Sum.inr 0))
    let v : Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F := bv F (Sum.inr (Sum.inr 1))
    ∀ z₀ t₀ : GL (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F,
    (z₀ : Matrix _ _ F) = ofColumns F (Sum.elim ![e 0 + f 1, f 0 + e 1, e 2]
      (Sum.elim ![e 1, e 0, f 2] ![α • u + b⁻¹ • v, (c / b) • u + (α + 1) • v])) →
    (t₀ : Matrix _ _ F) = ofColumns F (Sum.elim ![e 1, e 0 + e 1, e 2]
      (Sum.elim ![f 0 + f 1, f 0, f 2] ![u, v])) →
    GenLeaf (StatedOmega (StatedQuadMinus 4 F b c)) z₀ t₀ := by
  intro e f u v z₀ t₀ hz ht
  have hch : CharP F 2 := k328r8g_charTwo hF
  have hb : b ≠ 0 := k328r8g_b_ne_zero hF b c hbc
  have hz' : (z₀ : Matrix _ _ F) = ofColumns F (k328r8g_zc b c α) := hz
  have ht' : (t₀ : Matrix _ _ F) = ofColumns F k328r8g_tc := ht
  have i1 : ∀ w : Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F,
      k328r8g_Q b c
        (((z₀ * t₀ ^ 2 : GL (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F) :
          Matrix (Fin 3 ⊕ Fin 3 ⊕ Fin 2) (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F) *ᵥ w) =
        k328r8g_Q b c w := by
    intro w
    rw [Units.val_mul, Units.val_pow_eq_pow_val, pow_two, ← Matrix.mulVec_mulVec,
      ← Matrix.mulVec_mulVec, hz', ht']
    rw [k328r8g_z0_iso b c α hb hα, k328r8g_t0_iso b c, k328r8g_t0_iso b c]
  have i2 : ∀ w : Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F,
      k328r8g_Q b c
        (((z₀ * t₀ : GL (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F) :
          Matrix (Fin 3 ⊕ Fin 3 ⊕ Fin 2) (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F) *ᵥ w) =
        k328r8g_Q b c w := by
    intro w
    rw [Units.val_mul, ← Matrix.mulVec_mulVec, hz', ht']
    rw [k328r8g_z0_iso b c α hb hα, k328r8g_t0_iso b c]
  have i3 : ∀ w : Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F,
      k328r8g_Q b c
        ((t₀ : Matrix (Fin 3 ⊕ Fin 3 ⊕ Fin 2) (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F) *ᵥ w) =
        k328r8g_Q b c w := by
    intro w
    rw [ht']
    exact k328r8g_t0_iso b c w
  have he1 : ((z₀ * t₀ ^ 2 : GL (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F) :
      Matrix (Fin 3 ⊕ Fin 3 ⊕ Fin 2) (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F) *ᵥ
        (k328r8g_e 2 : Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F) = k328r8g_e 2 :=
    k328r8g_s1_fix_e2 b c α z₀ t₀ hz' ht'
  have hf1 : ((z₀ * t₀ ^ 2 : GL (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F) :
      Matrix (Fin 3 ⊕ Fin 3 ⊕ Fin 2) (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F) *ᵥ
        (k328r8g_f 2 : Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F) = k328r8g_f 2 :=
    k328r8g_s1_fix_f2 b c α z₀ t₀ hz' ht'
  have he2 : ((z₀ * t₀ : GL (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F) :
      Matrix (Fin 3 ⊕ Fin 3 ⊕ Fin 2) (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F) *ᵥ
        (k328r8g_e 2 : Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F) = k328r8g_e 2 :=
    k328r8g_s2_fix_e2 b c α z₀ t₀ hz' ht'
  have hf2 : ((z₀ * t₀ : GL (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F) :
      Matrix (Fin 3 ⊕ Fin 3 ⊕ Fin 2) (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F) *ᵥ
        (k328r8g_f 2 : Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F) = k328r8g_f 2 :=
    k328r8g_s2_fix_f2 b c α z₀ t₀ hz' ht'
  have he3 : (t₀ : Matrix (Fin 3 ⊕ Fin 3 ⊕ Fin 2) (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F) *ᵥ
        (k328r8g_e 2 : Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F) = k328r8g_e 2 :=
    k328r8g_t0_fix_e2 b c t₀ ht'
  have hf3 : (t₀ : Matrix (Fin 3 ⊕ Fin 3 ⊕ Fin 2) (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F) *ᵥ
        (k328r8g_f 2 : Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F) = k328r8g_f 2 :=
    k328r8g_t0_fix_f2 b c t₀ ht'
  unfold GenLeaf
  refine le_antisymm
    (sup_le (sup_le (sup_le inf_le_left inf_le_left) inf_le_left) inf_le_left) ?_
  refine k328r8g_gen_le b c hbc (s1 := z₀ * t₀ ^ 2) (s2 := z₀ * t₀) (s3 := t₀)
    le_sup_right (le_sup_right.trans le_sup_left)
    (le_sup_right.trans (le_sup_left.trans le_sup_left)) i1 i2 i3 he1 hf1 he2 hf2 he3 hf3
    (fun a ha => k328r8g_s1_fix_A1 b c α z₀ t₀ hz' ht' ha)
    (fun a ha => k328r8g_s2_fix_A2 b c α z₀ t₀ hz' ht' ha)
    (fun a ha => k328r8g_t0_fix_A3 b c t₀ ht' ha)
end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328
