module

public import CFSG.LocalAnalysis.StandardType.GGSixSeventeenWitSpBasic
public import CFSG.ClassicalInvolution.Models.SymplecticPairs.Intrinsic

public section

namespace CFSG.StandardType

namespace WitClSp

open Matrix CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Models.SymplecticPairs
  CFSG.SeitzReduction.SymplecticPilot
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective)
open scoped MatrixGroups

variable {K : Type} [Field K] {n : ℕ}

theorem mat_apply_eq_mulVec (w : StatedSp n K) (a b : Fin n ⊕ Fin n) :
    mat n K w a b = (mat n K w *ᵥ Pi.single b 1) a :=
  (mulVec_single_one_apply _ b a).symm

theorem mat_par_row_of_fix (w : StatedSp n K) {x : Fin n ⊕ Fin n}
    (hx : mat n K w *ᵥ Pi.single x 1 = Pi.single x 1) (b : Fin n ⊕ Fin n) :
    mat n K w (par x) b = if b = par x then 1 else 0 := by
  have h := congrFun (congrFun (mat_transpose_mul_gram_mul w) x) b
  rw [transpose_mul_gram_mul_apply, CFSG.ClassicalInvolution.Models.SymplecticPairs.gram_apply] at h
  have hcol : ∀ c, mat n K w c x = if c = x then 1 else 0 := fun c => by
    rw [mat_apply_eq_mulVec, hx, Pi.single_apply]
  rw [Finset.sum_eq_single x (fun c _ hc => by rw [hcol c, ite_eq_right hc, zero_mul])
    (fun h => absurd (Finset.mem_univ x) h), hcol x, ite_eq_left rfl, one_mul] at h
  have hs : sgn K x ≠ 0 := sgn_ne_zero x
  by_cases hb : b = par x
  · rw [ite_eq_left hb] at h ⊢
    exact mul_left_cancel₀ hs (h.trans (mul_one _).symm)
  · rw [ite_eq_right hb] at h ⊢
    exact (mul_eq_zero.mp h).resolve_left hs

theorem diagSpEntry_mulSingle_of_ne {j : Fin n} (ζ : Kˣ) {a : Fin n ⊕ Fin n}
    (h₁ : a ≠ Sum.inl j) (h₂ : a ≠ Sum.inr j) :
    diagSpEntry (Pi.mulSingle j ζ) a = 1 := by
  rcases a with k | k
  · have hk : k ≠ j := fun h => h₁ (by rw [h])
    simp [diagSpEntry, Pi.mulSingle_eq_of_ne hk]
  · have hk : k ≠ j := fun h => h₂ (by rw [h])
    simp [diagSpEntry, Pi.mulSingle_eq_of_ne hk]

theorem commute_diagSp_one_of_fix (w : StatedSp n K) (j : Fin n)
    (h₁ : mat n K w *ᵥ Pi.single (Sum.inl j) 1 = Pi.single (Sum.inl j) 1)
    (h₂ : mat n K w *ᵥ Pi.single (Sum.inr j) 1 = Pi.single (Sum.inr j) 1) (ζ : Kˣ) :
    Commute w (diagSp K n (Pi.mulSingle j ζ)) := by
  rw [commute_diagSp_iff]
  intro a b hab
  have hne : a ≠ b := fun h => hab (by rw [h])
  have hcol : ∀ x, (x = Sum.inl j ∨ x = Sum.inr j) → ∀ c, mat n K w c x =
      if c = x then 1 else 0 := by
    rintro x (rfl | rfl) c
    · rw [mat_apply_eq_mulVec, h₁, Pi.single_apply]
    · rw [mat_apply_eq_mulVec, h₂, Pi.single_apply]
  by_cases hb : b = Sum.inl j ∨ b = Sum.inr j
  · rw [hcol b hb a, ite_eq_right hne]
  by_cases ha : a = Sum.inl j ∨ a = Sum.inr j
  · rcases ha with rfl | rfl
    · have := mat_par_row_of_fix w (x := Sum.inr j) h₂ b
      rw [par_inr] at this
      rw [this, ite_eq_right (fun h => hne h.symm)]
    · have := mat_par_row_of_fix w (x := Sum.inl j) h₁ b
      rw [par_inl] at this
      rw [this, ite_eq_right (fun h => hne h.symm)]
  · push Not at ha hb
    exact absurd (by rw [diagSpEntry_mulSingle_of_ne ζ ha.1 ha.2,
      diagSpEntry_mulSingle_of_ne ζ hb.1 hb.2]) hab

theorem sum_col_mul_eq_gram (w : StatedSp n K) (x' b : Fin n ⊕ Fin n)
    {col : Fin n ⊕ Fin n → K} (hcol : mat n K w *ᵥ Pi.single x' 1 = col) :
    ∑ c, col c * (sgn K c * mat n K w (par c) b) = gram K n x' b := by
  have h := congrFun (congrFun (mat_transpose_mul_gram_mul w) x') b
  rw [transpose_mul_gram_mul_apply] at h
  rw [← h]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [mat_apply_eq_mulVec w c x', hcol]

theorem sum_single_add_smul_mul {ι : Type} [Fintype ι] [DecidableEq ι] (a a' : ι) (c₀ : K)
    (X : ι → K) :
    ∑ c, (Pi.single a 1 + c₀ • Pi.single a' 1 : ι → K) c * X c = X a + c₀ * X a' := by
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul, Finset.sum_add_distrib,
    mul_assoc]
  rw [← Finset.mul_sum]
  simp [Pi.single_apply]

theorem diagSpEntry_two_inl {i j : Fin n} (ζ : Kˣ) {k : Fin n} (hk : k = i ∨ k = j)
    (hij : i ≠ j) :
    diagSpEntry (Pi.mulSingle i ζ * Pi.mulSingle j ζ) (Sum.inl k) = (ζ : K) := by
  rcases hk with rfl | rfl
  · simp [diagSpEntry, Pi.mulSingle_eq_of_ne hij]
  · simp [diagSpEntry, Pi.mulSingle_eq_of_ne (Ne.symm hij)]

theorem diagSpEntry_two_inr {i j : Fin n} (ζ : Kˣ) {k : Fin n} (hk : k = i ∨ k = j)
    (hij : i ≠ j) :
    diagSpEntry (Pi.mulSingle i ζ * Pi.mulSingle j ζ) (Sum.inr k) = ((ζ⁻¹ : Kˣ) : K) := by
  rcases hk with rfl | rfl
  · simp [diagSpEntry, Pi.mulSingle_eq_of_ne hij]
  · simp [diagSpEntry, Pi.mulSingle_eq_of_ne (Ne.symm hij)]

theorem diagSpEntry_two_of_ne {i j : Fin n} (ζ : Kˣ) {a : Fin n ⊕ Fin n}
    (h₁ : a ≠ Sum.inl i) (h₂ : a ≠ Sum.inl j) (h₃ : a ≠ Sum.inr i) (h₄ : a ≠ Sum.inr j) :
    diagSpEntry (Pi.mulSingle i ζ * Pi.mulSingle j ζ) a = 1 := by
  rcases a with k | k
  · have hi : k ≠ i := fun h => h₁ (by rw [h])
    have hj : k ≠ j := fun h => h₂ (by rw [h])
    simp [diagSpEntry, Pi.mulSingle_eq_of_ne hi, Pi.mulSingle_eq_of_ne hj]
  · have hi : k ≠ i := fun h => h₃ (by rw [h])
    have hj : k ≠ j := fun h => h₄ (by rw [h])
    simp [diagSpEntry, Pi.mulSingle_eq_of_ne hi, Pi.mulSingle_eq_of_ne hj]

theorem commute_diagSp_two_of_cols (w : StatedSp n K) {i j : Fin n} (hij : i ≠ j) (c : K)
    (h₁ : mat n K w *ᵥ Pi.single (Sum.inl i) 1 = Pi.single (Sum.inl i) 1)
    (h₂ : mat n K w *ᵥ Pi.single (Sum.inl j) 1 =
      Pi.single (Sum.inl j) 1 + c • Pi.single (Sum.inl i) 1)
    (h₃ : mat n K w *ᵥ Pi.single (Sum.inr i) 1 =
      Pi.single (Sum.inr i) 1 + c • Pi.single (Sum.inr j) 1)
    (h₄ : mat n K w *ᵥ Pi.single (Sum.inr j) 1 = Pi.single (Sum.inr j) 1) (ζ : Kˣ) :
    Commute w (diagSp K n (Pi.mulSingle i ζ * Pi.mulSingle j ζ)) := by
  have hAi := diagSpEntry_two_inl ζ (Or.inl rfl) hij
  have hAj := diagSpEntry_two_inl ζ (Or.inr rfl) hij
  have hBi := diagSpEntry_two_inr ζ (Or.inl rfl) hij
  have hBj := diagSpEntry_two_inr ζ (Or.inr rfl) hij
  have hji : (Sum.inl j : Fin n ⊕ Fin n) ≠ Sum.inl i := fun h => hij (Sum.inl_injective h).symm
  have hji' : (Sum.inr j : Fin n ⊕ Fin n) ≠ Sum.inr i := fun h => hij (Sum.inr_injective h).symm
  have hrows : ∀ b, b ≠ Sum.inl i → b ≠ Sum.inl j → b ≠ Sum.inr i → b ≠ Sum.inr j →
      mat n K w (Sum.inl i) b = 0 ∧ mat n K w (Sum.inl j) b = 0 ∧
        mat n K w (Sum.inr i) b = 0 ∧ mat n K w (Sum.inr j) b = 0 := by
    intro b b₁ b₂ b₃ b₄
    have r₁ := mat_par_row_of_fix w h₁ b
    have r₄ := mat_par_row_of_fix w h₄ b
    rw [par_inl, ite_eq_right b₃] at r₁
    rw [par_inr, ite_eq_right b₂] at r₄
    have e₂ := sum_col_mul_eq_gram w (Sum.inl j) b h₂
    have e₃ := sum_col_mul_eq_gram w (Sum.inr i) b h₃
    rw [sum_single_add_smul_mul, CFSG.ClassicalInvolution.Models.SymplecticPairs.gram_apply,
      par_inl, par_inl, ite_eq_right b₄, sgn_inl, sgn_inl, r₁] at e₂
    rw [sum_single_add_smul_mul, CFSG.ClassicalInvolution.Models.SymplecticPairs.gram_apply,
      par_inr, par_inr, ite_eq_right b₁, sgn_inr, sgn_inr, r₄] at e₃
    refine ⟨?_, r₄, r₁, ?_⟩
    · linear_combination -e₃
    · linear_combination e₂
  rw [commute_diagSp_iff]
  intro a b hab
  have hne : a ≠ b := fun h => hab (by rw [h])
  have col : ∀ x : Fin n ⊕ Fin n, ∀ v : Fin n ⊕ Fin n → K,
      mat n K w *ᵥ Pi.single x 1 = v → mat n K w a x = v a := fun x v hv => by
    rw [mat_apply_eq_mulVec, hv]
  by_cases hb₁ : b = Sum.inl i
  · subst hb₁
    rw [col _ _ h₁, Pi.single_apply, ite_eq_right hne]
  by_cases hb₂ : b = Sum.inl j
  · subst hb₂
    rw [col _ _ h₂, Pi.add_apply, Pi.smul_apply, Pi.single_apply, Pi.single_apply,
      ite_eq_right hne, smul_eq_mul]
    by_cases ha : a = Sum.inl i
    · subst ha
      exact absurd (hAi.trans hAj.symm) hab
    · rw [ite_eq_right ha, mul_zero, zero_add]
  by_cases hb₃ : b = Sum.inr i
  · subst hb₃
    rw [col _ _ h₃, Pi.add_apply, Pi.smul_apply, Pi.single_apply, Pi.single_apply,
      ite_eq_right hne, smul_eq_mul]
    by_cases ha : a = Sum.inr j
    · subst ha
      exact absurd (hBj.trans hBi.symm) hab
    · rw [ite_eq_right ha, mul_zero, zero_add]
  by_cases hb₄ : b = Sum.inr j
  · subst hb₄
    rw [col _ _ h₄, Pi.single_apply, ite_eq_right hne]
  obtain ⟨r₁, r₂, r₃, r₄⟩ := hrows b hb₁ hb₂ hb₃ hb₄
  by_cases ha₁ : a = Sum.inl i
  · rw [ha₁, r₁]
  by_cases ha₂ : a = Sum.inl j
  · rw [ha₂, r₂]
  by_cases ha₃ : a = Sum.inr i
  · rw [ha₃, r₃]
  by_cases ha₄ : a = Sum.inr j
  · rw [ha₄, r₄]
  exact absurd (by rw [diagSpEntry_two_of_ne ζ ha₁ ha₂ ha₃ ha₄,
    diagSpEntry_two_of_ne ζ hb₁ hb₂ hb₃ hb₄]) hab

section Nil

@[expose] noncomputable def nilL (v : StatedSp n K) :
    (Fin n ⊕ Fin n → K) →ₗ[K] (Fin n ⊕ Fin n → K) :=
  Matrix.mulVecLin (mat n K v - 1)

theorem nilL_apply (v : StatedSp n K) (z : Fin n ⊕ Fin n → K) :
    nilL v z = mat n K v *ᵥ z - z := by
  rw [nilL, Matrix.mulVecLin_apply, Matrix.sub_mulVec, Matrix.one_mulVec]

theorem form_sub_left (a b w : Fin n ⊕ Fin n → K) : form (a - b) w = form a w - form b w := by
  simp [form, sub_dotProduct]

theorem form_sub_right (w a b : Fin n ⊕ Fin n → K) : form w (a - b) = form w a - form w b := by
  simp [form, Matrix.mulVec_sub, dotProduct_sub]

variable {v : StatedSp n K}

theorem mulVec_mulVec_self (hv : v * v = 1) (z : Fin n ⊕ Fin n → K) :
    mat n K v *ᵥ (mat n K v *ᵥ z) = z := by
  rw [Matrix.mulVec_mulVec, ← map_mul, hv, map_one, Matrix.one_mulVec]

theorem mulVec_eq_add_nilL (z : Fin n ⊕ Fin n → K) : mat n K v *ᵥ z = z + nilL v z := by
  rw [nilL_apply, add_sub_cancel]

theorem nilL_nilL [CharP K 2] (hv : v * v = 1) (z : Fin n ⊕ Fin n → K) :
    nilL v (nilL v z) = 0 := by
  rw [nilL_apply, nilL_apply, Matrix.mulVec_sub, mulVec_mulVec_self hv]
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  funext a
  simp only [Pi.sub_apply, Pi.zero_apply]
  linear_combination (z a - (mat n K v *ᵥ z) a) * h2

theorem form_nilL_left (hv : v * v = 1) (z w : Fin n ⊕ Fin n → K) :
    form (nilL v z) w = form z (nilL v w) := by
  rw [nilL_apply, nilL_apply, form_sub_left, form_sub_right]
  congr 1
  rw [← form_mulVec v (mat n K v *ᵥ z) w, mulVec_mulVec_self hv]

theorem form_nilL_nilL [CharP K 2] (hv : v * v = 1) (z w : Fin n ⊕ Fin n → K) :
    form (nilL v z) (nilL v w) = 0 := by
  rw [form_nilL_left hv, nilL_nilL hv, form_zero_right]

theorem form_nilL_comm [CharP K 2] (hv : v * v = 1) (z w : Fin n ⊕ Fin n → K) :
    form z (nilL v w) = form w (nilL v z) := by
  rw [← form_nilL_left hv, form_antisymm, CharTwo.neg_eq]

theorem mem_fixSpace_iff_nilL {z : Fin n ⊕ Fin n → K} : z ∈ fixSpace v ↔ nilL v z = 0 := by
  rw [mem_fixSpace, nilL_apply, sub_eq_zero]

theorem quad_add [CharP K 2] (hv : v * v = 1) (z w : Fin n ⊕ Fin n → K) :
    form (z + w) (nilL v (z + w)) = form z (nilL v z) + form w (nilL v w) := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  rw [map_add, form_add_left, form_add_right, form_add_right, form_nilL_comm hv z w]
  linear_combination form w (nilL v z) * h2

theorem quad_smul (c : K) (z : Fin n ⊕ Fin n → K) :
    form (c • z) (nilL v (c • z)) = c ^ 2 * form z (nilL v z) := by
  rw [map_smul, form_smul_left, form_smul_right]
  ring

@[expose] noncomputable def quadKer [CharP K 2] (hv : v * v = 1) :
    Submodule K (Fin n ⊕ Fin n → K) where
  carrier := {z | form z (nilL v z) = 0}
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq] at ha hb ⊢
    rw [quad_add hv, ha, hb, add_zero]
  zero_mem' := by simp [form_zero_left]
  smul_mem' := by
    intro c z hz
    simp only [Set.mem_ofPred_eq] at hz ⊢
    rw [quad_smul, hz, mul_zero]

theorem mem_quadKer [CharP K 2] (hv : v * v = 1) {z : Fin n ⊕ Fin n → K} :
    z ∈ quadKer hv ↔ form z (nilL v z) = 0 := Iff.rfl

theorem finrank_ambient : Module.finrank K (Fin n ⊕ Fin n → K) = 2 * n := by
  rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]
  ring

theorem finrank_quadKer [Finite K] [CharP K 2] (hv : v * v = 1) :
    2 * n ≤ Module.finrank K (quadKer hv) + 1 := by
  by_cases htop : ∀ z, form z (nilL v z) = 0
  · have : quadKer hv = ⊤ := eq_top_iff.mpr fun z _ => htop z
    rw [this, finrank_top, finrank_ambient]
    omega
  push Not at htop
  obtain ⟨z₀, hz₀⟩ := htop
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hsup : quadKer hv ⊔ Submodule.span K {z₀} = ⊤ := by
    refine eq_top_iff.mpr fun z _ => ?_
    obtain ⟨c, hc⟩ := isSquare_of_charTwo' (form z (nilL v z) / form z₀ (nilL v z₀))
    have hmem : z - c • z₀ ∈ quadKer hv := by
      rw [mem_quadKer, sub_eq_add_neg, quad_add hv, ← neg_smul, quad_smul]
      have : (-c) ^ 2 * form z₀ (nilL v z₀) = form z (nilL v z) := by
        rw [neg_sq, sq, ← hc, div_mul_cancel₀ _ hz₀]
      rw [this]
      linear_combination form z (nilL v z) * h2
    have := Submodule.add_mem_sup hmem
      (Submodule.smul_mem _ c (Submodule.mem_span_singleton_self z₀))
    simpa using this
  have h := Submodule.finrank_add_le_finrank_add_finrank (quadKer hv) (Submodule.span K {z₀})
  rw [hsup, finrank_top, finrank_ambient] at h
  have h1 := finrank_span_le_card (R := K) ({z₀} : Set (Fin n ⊕ Fin n → K))
  rw [Set.toFinset_singleton, Finset.card_singleton] at h1
  omega

end Nil

section Pair

variable {v : StatedSp n K}

theorem finrank_fixSpace_le (hiso : ∀ x ∈ fixSpace v, ∀ y ∈ fixSpace v, form x y = 0) :
    Module.finrank K (fixSpace v) ≤ n := by
  have hle : fixSpace v ≤ (Matrix.toBilin' (Matrix.J (Fin n) K)).orthogonal (fixSpace v) := by
    intro z hz
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro w hw
    rw [toBilin'_J_apply, hiso w hw z hz, neg_zero]
  have h1 := Submodule.finrank_mono hle
  rw [LinearMap.BilinForm.finrank_orthogonal nondegenerate_toBilin'_J, finrank_ambient] at h1
  omega

theorem exists_quad_pair_aux [Finite K] [CharP K 2] (hv : v * v = 1) (hn : 3 ≤ n)
    (hiso : ∀ x ∈ fixSpace v, ∀ y ∈ fixSpace v, form x y = 0) :
    ∃ f₁ f₂ : Fin n ⊕ Fin n → K, form f₁ (nilL v f₁) = 0 ∧ form f₂ (nilL v f₂) = 0 ∧
      form f₁ (nilL v f₂) ≠ 0 := by
  by_contra hcon
  push Not at hcon
  have hmap : (quadKer hv).map (nilL v) ≤
      (Matrix.toBilin' (Matrix.J (Fin n) K)).orthogonal (quadKer hv) := by
    rintro _ ⟨z, hz, rfl⟩
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro w hw
    rw [toBilin'_J_apply, hcon w z hw hz, neg_zero]
  have h1 := Submodule.finrank_mono hmap
  rw [LinearMap.BilinForm.finrank_orthogonal nondegenerate_toBilin'_J, finrank_ambient] at h1
  have h2 := finrank_quadKer hv
  have h3 := LinearMap.finrank_range_add_finrank_ker ((nilL v).comp (quadKer hv).subtype)
  rw [LinearMap.range_comp, Submodule.range_subtype] at h3
  have h4 : Module.finrank K (LinearMap.ker ((nilL v).comp (quadKer hv).subtype)) ≤
      Module.finrank K (fixSpace v) := by
    refine LinearMap.finrank_le_finrank_of_injective
      (f := LinearMap.codRestrict (fixSpace v) ((quadKer hv).subtype.comp
        (LinearMap.ker ((nilL v).comp (quadKer hv).subtype)).subtype)
        fun z => mem_fixSpace_iff_nilL.mpr (LinearMap.mem_ker.mp z.2)) ?_
    intro a b hab
    have := congrArg (fun x : fixSpace v => (x : Fin n ⊕ Fin n → K)) hab
    exact Subtype.ext (Subtype.ext this)
  have h5 := finrank_fixSpace_le hiso
  omega

theorem exists_quad_pair [Finite K] [CharP K 2] (hv : v * v = 1) (hn : 3 ≤ n)
    (hiso : ∀ x ∈ fixSpace v, ∀ y ∈ fixSpace v, form x y = 0) :
    ∃ f₁ f₂ : Fin n ⊕ Fin n → K, form f₁ (nilL v f₁) = 0 ∧ form f₂ (nilL v f₂) = 0 ∧
      form f₁ (nilL v f₂) ≠ 0 ∧ form f₁ f₂ = 0 := by
  obtain ⟨f₁, f₂, h₁, h₂, ha⟩ := exists_quad_pair_aux hv hn hiso
  refine ⟨f₁, f₂ + (-(form f₁ f₂ / form f₁ (nilL v f₂))) • nilL v f₂, h₁, ?_, ?_, ?_⟩
  · rw [quad_add hv, h₂, quad_smul, nilL_nilL hv, form_zero_right, mul_zero, add_zero]
  · rw [map_add, map_smul, nilL_nilL hv, smul_zero, add_zero]
    exact ha
  · rw [form_add_right, form_smul_right, neg_mul, div_mul_cancel₀ _ ha, add_neg_cancel]

end Pair

section Main

theorem exists_conj_commute_torusWit [Finite K] [CharP K 2] {m : ℕ}
    (v : StatedSp (m + 1 + 1 + 1) K) (hv : v * v = 1) (ζ : Kˣ) :
    ∃ g : StatedSp (m + 1 + 1 + 1) K,
      Commute (g * v * g⁻¹) (diagSp K (m + 1 + 1 + 1) (Pi.mulSingle 0 ζ)) ∨
        Commute (g * v * g⁻¹)
          (diagSp K (m + 1 + 1 + 1) (Pi.mulSingle 0 ζ * Pi.mulSingle 1 ζ)) := by
  by_cases ha : ∃ x ∈ fixSpace v, ∃ y ∈ fixSpace v, form x y ≠ 0
  · obtain ⟨x, hx, y, hy, hxy⟩ := ha
    obtain ⟨h, hh₁, hh₂⟩ := exists_sp_apply_eq (m := m + 1 + 1) x ((form x y)⁻¹ • y)
      (by rw [form_smul_right, inv_mul_cancel₀ hxy])
    refine ⟨h⁻¹, Or.inl (commute_diagSp_one_of_fix _ 0 ?_ ?_ ζ)⟩
    · rw [inv_inv, map_mul, map_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hh₁,
        mem_fixSpace.mp hx, ← hh₁, mulVec_inv_mulVec]
    · rw [inv_inv, map_mul, map_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hh₂,
        mem_fixSpace.mp (Submodule.smul_mem _ _ hy), ← hh₂, mulVec_inv_mulVec]
  push Not at ha
  obtain ⟨f₁, f₂, hq₁, hq₂, ha0, ho⟩ := exists_quad_pair hv (by omega) ha
  have hsym : form f₂ (nilL v f₁) = form f₁ (nilL v f₂) := form_nilL_comm hv f₂ f₁
  have hN₂ : nilL v (nilL v f₂) = 0 := nilL_nilL hv f₂
  have hN₁ : nilL v (nilL v f₁) = 0 := nilL_nilL hv f₁
  have hl : form (nilL v f₂) f₁ = form f₁ (nilL v f₂) := by rw [form_nilL_left hv, hsym]
  have hl₂ : form (nilL v f₂) f₂ = 0 := by rw [form_nilL_left hv, hq₂]
  have hll : form (nilL v f₂) (nilL v f₁) = 0 := form_nilL_nilL hv f₂ f₁
  generalize hadef : form f₁ (nilL v f₂) = a at hsym ha0 hl
  obtain ⟨b, hb, hb₁, hb₂, hb₃, hb₄⟩ := exists_symplectic_basis_two (m := m + 1)
    (a⁻¹ • nilL v f₂) f₁ f₂ (a⁻¹ • nilL v f₁)
    (by rw [form_smul_left, hl, inv_mul_cancel₀ ha0])
    (by rw [form_smul_right, hsym, inv_mul_cancel₀ ha0])
    (by rw [form_smul_left, hl₂, mul_zero])
    (by rw [form_smul_left, form_smul_right, hll, mul_zero, mul_zero])
    ho (by rw [form_smul_right, hq₁, mul_zero])
  have hcol : ∀ x, mat _ K (ofSymplecticBasis b hb) *ᵥ Pi.single x 1 = b x :=
    mat_ofSymplecticBasis_mulVec_single b hb
  have hinv : ∀ x, mat _ K (ofSymplecticBasis b hb)⁻¹ *ᵥ b x = Pi.single x 1 := fun x => by
    rw [← hcol x, mulVec_inv_mulVec]
  have hconj : ∀ x, mat _ K ((ofSymplecticBasis b hb)⁻¹ * v * (ofSymplecticBasis b hb)⁻¹⁻¹) *ᵥ
      Pi.single x 1 = mat _ K (ofSymplecticBasis b hb)⁻¹ *ᵥ (mat _ K v *ᵥ b x) := fun x => by
    rw [inv_inv, map_mul, map_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hcol]
  have hsmul₂ : nilL v f₂ = a • b (Sum.inl 0) := by
    rw [hb₁, smul_smul, mul_inv_cancel₀ ha0, one_smul]
  have hsmul₁ : nilL v f₁ = a • b (Sum.inr 1) := by
    rw [hb₄, smul_smul, mul_inv_cancel₀ ha0, one_smul]
  have hf₂ : mat _ K (ofSymplecticBasis b hb)⁻¹ *ᵥ f₂ = Pi.single (Sum.inl 1) 1 := by
    rw [← hb₃, hinv]
  have hf₁ : mat _ K (ofSymplecticBasis b hb)⁻¹ *ᵥ f₁ = Pi.single (Sum.inr 0) 1 := by
    rw [← hb₂, hinv]
  have h01 : (0 : Fin (m + 1 + 1 + 1)) ≠ 1 := by simp
  refine ⟨(ofSymplecticBasis b hb)⁻¹, Or.inr (commute_diagSp_two_of_cols _ (i := 0) (j := 1)
    h01 a ?_ ?_ ?_ ?_ ζ)⟩
  · rw [hconj, mulVec_eq_add_nilL (v := v), hb₁, map_smul, hN₂, smul_zero, add_zero, ← hb₁,
      hinv]
  · rw [hconj, mulVec_eq_add_nilL (v := v), hb₃, hsmul₂, Matrix.mulVec_add, Matrix.mulVec_smul,
      hinv, hf₂]
  · rw [hconj, mulVec_eq_add_nilL (v := v), hb₂, hsmul₁, Matrix.mulVec_add, Matrix.mulVec_smul,
      hinv, hf₁]
  · rw [hconj, mulVec_eq_add_nilL (v := v), hb₄, map_smul, hN₁, smul_zero, add_zero, ← hb₄,
      hinv]

end Main

section Swap

theorem mat_permSp_mulVec_single (π : Equiv.Perm (Fin n)) (x : Fin n ⊕ Fin n) :
    mat n K (permSp K π) *ᵥ Pi.single x 1 = Pi.single (Sum.map π π x) 1 := by
  funext a
  rw [mulVec_single_one_apply, mat_permSp, spIncl_apply, Pi.single_apply]

theorem mem_suppGroup_compl_of_fix {w : StatedSp n K} {k : Fin n}
    (h₁ : mat n K w *ᵥ Pi.single (Sum.inl k) 1 = Pi.single (Sum.inl k) 1)
    (h₂ : mat n K w *ᵥ Pi.single (Sum.inr k) 1 = Pi.single (Sum.inr k) 1) :
    w ∈ suppGroup (coords k)ᶜ := by
  rw [mem_suppGroup_iff (parClosed_coords k).compl]
  intro t ht r
  simp only [Set.mem_compl_iff, not_not, mem_coords] at ht
  rcases ht with rfl | rfl
  · rw [mat_apply_eq_mulVec, h₁, Pi.single_apply, Matrix.one_apply]
  · rw [mat_apply_eq_mulVec, h₂, Pi.single_apply, Matrix.one_apply]

theorem commute_longBlock_of_fix {w : StatedSp n K} {k : Fin n}
    (h₁ : mat n K w *ᵥ Pi.single (Sum.inl k) 1 = Pi.single (Sum.inl k) 1)
    (h₂ : mat n K w *ᵥ Pi.single (Sum.inr k) 1 = Pi.single (Sum.inr k) 1) (T : SL(2, K)) :
    Commute (longBlock K n k T) w :=
  commute_suppGroup_compl (by rw [← range_longBlock]; exact ⟨T, rfl⟩)
    (mem_suppGroup_compl_of_fix h₁ h₂)

theorem parClosed_coords_union (i j : Fin n) : ParClosed (coords i ∪ coords j) := by
  rintro a (ha | ha)
  · exact Or.inl (parClosed_coords i a ha)
  · exact Or.inr (parClosed_coords j a ha)

theorem longBlock_mem_suppGroup (k : Fin n) (T : SL(2, K)) :
    longBlock K n k T ∈ suppGroup (coords k) := by
  rw [← range_longBlock]
  exact ⟨T, rfl⟩

theorem commute_longBlock_two_of_swap {w : StatedSp n K} {i j : Fin n} (hij : i ≠ j)
    (h₁ : mat n K w *ᵥ Pi.single (Sum.inl i) 1 = Pi.single (Sum.inl j) 1)
    (h₂ : mat n K w *ᵥ Pi.single (Sum.inr i) 1 = Pi.single (Sum.inr j) 1)
    (h₃ : mat n K w *ᵥ Pi.single (Sum.inl j) 1 = Pi.single (Sum.inl i) 1)
    (h₄ : mat n K w *ᵥ Pi.single (Sum.inr j) 1 = Pi.single (Sum.inr i) 1) (T : SL(2, K)) :
    Commute (longBlock K n i T * longBlock K n j T) w := by
  obtain ⟨P, hP⟩ : ∃ P : StatedSp n K, P = permSp K (Equiv.swap i j) := ⟨_, rfl⟩
  have hPcol : ∀ x, mat n K P *ᵥ Pi.single x 1 =
      Pi.single (Sum.map (Equiv.swap i j) (Equiv.swap i j) x) 1 := fun x => by
    rw [hP, mat_permSp_mulVec_single]
  have hPi : ∀ x y, mat n K P *ᵥ Pi.single x 1 = Pi.single y 1 →
      mat n K P⁻¹ *ᵥ Pi.single y 1 = Pi.single x 1 := fun x y h => by
    rw [← h, mulVec_inv_mulVec]
  have hfix : ∀ x, x ∈ coords i ∪ coords j →
      mat n K (P⁻¹ * w) *ᵥ Pi.single x 1 = Pi.single x 1 := by
    intro x hx
    simp only [Set.mem_union, mem_coords] at hx
    rw [map_mul, ← Matrix.mulVec_mulVec]
    rcases hx with (rfl | rfl) | (rfl | rfl)
    · rw [h₁]
      exact hPi _ _ (by rw [hPcol]; simp)
    · rw [h₂]
      exact hPi _ _ (by rw [hPcol]; simp)
    · rw [h₃]
      exact hPi _ _ (by rw [hPcol]; simp)
    · rw [h₄]
      exact hPi _ _ (by rw [hPcol]; simp)
  have hw' : P⁻¹ * w ∈ suppGroup (coords i ∪ coords j)ᶜ := by
    rw [mem_suppGroup_iff (parClosed_coords_union i j).compl]
    intro t ht r
    rw [Set.mem_compl_iff, not_not] at ht
    rw [mat_apply_eq_mulVec, hfix t ht, Pi.single_apply, Matrix.one_apply]
  have hX : longBlock K n i T * longBlock K n j T ∈ suppGroup (coords i ∪ coords j) :=
    Subgroup.mul_mem _ (suppGroup_mono Set.subset_union_left (longBlock_mem_suppGroup i T))
      (suppGroup_mono Set.subset_union_right (longBlock_mem_suppGroup j T))
  have hXw' := commute_suppGroup_compl hX hw'
  have hji : Commute (longBlock K n j T) (longBlock K n i T) :=
    commute_suppGroup_compl (longBlock_mem_suppGroup j T)
      (suppGroup_mono (coords_subset_compl hij) (longBlock_mem_suppGroup i T))
  have hc : P * (longBlock K n i T * longBlock K n j T) * P⁻¹ =
      longBlock K n i T * longBlock K n j T := by
    rw [show P * (longBlock K n i T * longBlock K n j T) * P⁻¹ =
        (P * longBlock K n i T * P⁻¹) * (P * longBlock K n j T * P⁻¹) by group, hP,
      conj_permSp_longBlock, conj_permSp_longBlock, Equiv.swap_apply_left,
      Equiv.swap_apply_right]
    exact hji.eq
  have hXP : Commute (longBlock K n i T * longBlock K n j T) P :=
    (mul_inv_eq_iff_eq_mul.mp hc).symm
  have := hXP.mul_right hXw'
  rwa [mul_inv_cancel_left] at this

theorem exists_conj_fix_or_swap [Finite K] [CharP K 2] {m : ℕ}
    (v : StatedSp (m + 1 + 1 + 1) K) (hv : v * v = 1) :
    ∃ g : StatedSp (m + 1 + 1 + 1) K,
      (mat _ K (g * v * g⁻¹) *ᵥ Pi.single (Sum.inl 0) 1 = Pi.single (Sum.inl 0) 1 ∧
        mat _ K (g * v * g⁻¹) *ᵥ Pi.single (Sum.inr 0) 1 = Pi.single (Sum.inr 0) 1) ∨
      (mat _ K (g * v * g⁻¹) *ᵥ Pi.single (Sum.inl 0) 1 = Pi.single (Sum.inl 1) 1 ∧
        mat _ K (g * v * g⁻¹) *ᵥ Pi.single (Sum.inr 0) 1 = Pi.single (Sum.inr 1) 1 ∧
        mat _ K (g * v * g⁻¹) *ᵥ Pi.single (Sum.inl 1) 1 = Pi.single (Sum.inl 0) 1 ∧
        mat _ K (g * v * g⁻¹) *ᵥ Pi.single (Sum.inr 1) 1 = Pi.single (Sum.inr 0) 1) := by
  by_cases ha : ∃ x ∈ fixSpace v, ∃ y ∈ fixSpace v, form x y ≠ 0
  · obtain ⟨x, hx, y, hy, hxy⟩ := ha
    obtain ⟨h, hh₁, hh₂⟩ := exists_sp_apply_eq (m := m + 1 + 1) x ((form x y)⁻¹ • y)
      (by rw [form_smul_right, inv_mul_cancel₀ hxy])
    refine ⟨h⁻¹, Or.inl ⟨?_, ?_⟩⟩
    · rw [inv_inv, map_mul, map_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hh₁,
        mem_fixSpace.mp hx, ← hh₁, mulVec_inv_mulVec]
    · rw [inv_inv, map_mul, map_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hh₂,
        mem_fixSpace.mp (Submodule.smul_mem _ _ hy), ← hh₂, mulVec_inv_mulVec]
  push Not at ha
  obtain ⟨f₁, f₂, hq₁, hq₂, ha0, ho⟩ := exists_quad_pair hv (by omega) ha
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hsym : form f₂ (nilL v f₁) = form f₁ (nilL v f₂) := form_nilL_comm hv f₂ f₁
  have hl : form (nilL v f₂) f₁ = form f₁ (nilL v f₂) := by rw [form_nilL_left hv, hsym]
  have hl₁ : form (nilL v f₁) f₂ = form f₁ (nilL v f₂) := form_nilL_left hv f₁ f₂
  have hl₁₁ : form (nilL v f₁) f₁ = 0 := by rw [form_nilL_left hv, hq₁]
  have hll : form (nilL v f₁) (nilL v f₂) = 0 := form_nilL_nilL hv f₁ f₂
  have ho' : form f₂ f₁ = 0 := by rw [form_antisymm, ho, neg_zero]
  generalize hadef : form f₁ (nilL v f₂) = a at hsym ha0 hl hl₁
  obtain ⟨b, hb, hb₁, hb₂, hb₃, hb₄⟩ := exists_symplectic_basis_two (m := m + 1)
    f₂ (a⁻¹ • (f₁ + nilL v f₁)) (f₂ + nilL v f₂) (a⁻¹ • f₁)
    (by rw [form_smul_right, form_add_right, ho', hsym, zero_add, inv_mul_cancel₀ ha0])
    (by rw [form_smul_right, form_add_left, ho', hl, zero_add, inv_mul_cancel₀ ha0])
    (by rw [form_add_right, form_self, hq₂, add_zero])
    (by rw [form_smul_right, ho', mul_zero])
    (by
      rw [form_smul_left, form_add_left, form_add_right, form_add_right, ho, hadef, hl₁, hll]
      linear_combination a⁻¹ * a * h2)
    (by rw [form_smul_left, form_smul_right, form_add_left, form_self, hl₁₁, add_zero,
      mul_zero, mul_zero])
  have hcol : ∀ x, mat _ K (ofSymplecticBasis b hb) *ᵥ Pi.single x 1 = b x :=
    mat_ofSymplecticBasis_mulVec_single b hb
  have hinv : ∀ x, mat _ K (ofSymplecticBasis b hb)⁻¹ *ᵥ b x = Pi.single x 1 := fun x => by
    rw [← hcol x, mulVec_inv_mulVec]
  have hconj : ∀ x, mat _ K ((ofSymplecticBasis b hb)⁻¹ * v * (ofSymplecticBasis b hb)⁻¹⁻¹) *ᵥ
      Pi.single x 1 = mat _ K (ofSymplecticBasis b hb)⁻¹ *ᵥ (mat _ K v *ᵥ b x) := fun x => by
    rw [inv_inv, map_mul, map_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hcol]
  refine ⟨(ofSymplecticBasis b hb)⁻¹, Or.inr ⟨?_, ?_, ?_, ?_⟩⟩
  · rw [hconj, hb₁, mulVec_eq_add_nilL (v := v), ← hb₃, hinv]
  · rw [hconj, hb₂, ← mulVec_eq_add_nilL (v := v), Matrix.mulVec_smul, mulVec_mulVec_self hv,
      ← hb₄, hinv]
  · rw [hconj, hb₃, ← mulVec_eq_add_nilL (v := v), mulVec_mulVec_self hv, ← hb₁, hinv]
  · rw [hconj, hb₄, Matrix.mulVec_smul, mulVec_eq_add_nilL (v := v), ← hb₂, hinv]

end Swap

end WitClSp

end CFSG.StandardType
