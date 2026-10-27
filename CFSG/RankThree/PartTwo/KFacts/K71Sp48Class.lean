module

public import CFSG.RankThree.PartTwo.KFacts.K71InnerSp4

public section

namespace CFSG.RankThree.PartTwo.KFacts

open CFSG CFSG.Assembly.LowTwoRank
open Matrix

section Form

variable {F : Type} [Field F]

@[expose] def spForm (u v : Fin 2 ⊕ Fin 2 → F) : F :=
  u ⬝ᵥ ((fromBlocks 0 1 (-1) 0 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *ᵥ v)

theorem spForm_apply (u v : Fin 2 ⊕ Fin 2 → F) :
    spForm u v = u (.inl 0) * v (.inr 0) + u (.inl 1) * v (.inr 1) - u (.inr 0) * v (.inl 0) -
      u (.inr 1) * v (.inl 1) := by
  simp [spForm, dotProduct, mulVec, Fintype.sum_sum_type, Fin.sum_univ_two, one_apply]
  ring

theorem spForm_self (u : Fin 2 ⊕ Fin 2 → F) : spForm u u = 0 := by
  rw [spForm_apply]
  ring

theorem spForm_swap (u v : Fin 2 ⊕ Fin 2 → F) : spForm v u = -spForm u v := by
  rw [spForm_apply, spForm_apply]
  ring

theorem spForm_add_left (u u' v : Fin 2 ⊕ Fin 2 → F) :
    spForm (u + u') v = spForm u v + spForm u' v := by
  simp only [spForm_apply, Pi.add_apply]
  ring

theorem spForm_add_right (u v v' : Fin 2 ⊕ Fin 2 → F) :
    spForm u (v + v') = spForm u v + spForm u v' := by
  simp only [spForm_apply, Pi.add_apply]
  ring

theorem spForm_sub_left (u u' v : Fin 2 ⊕ Fin 2 → F) :
    spForm (u - u') v = spForm u v - spForm u' v := by
  simp only [spForm_apply, Pi.sub_apply]
  ring

theorem spForm_sub_right (u v v' : Fin 2 ⊕ Fin 2 → F) :
    spForm u (v - v') = spForm u v - spForm u v' := by
  simp only [spForm_apply, Pi.sub_apply]
  ring

theorem spForm_smul_left (c : F) (u v : Fin 2 ⊕ Fin 2 → F) :
    spForm (c • u) v = c * spForm u v := by
  simp only [spForm_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem spForm_smul_right (c : F) (u v : Fin 2 ⊕ Fin 2 → F) :
    spForm u (c • v) = c * spForm u v := by
  simp only [spForm_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem spForm_mulVec {g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F}
    (hg : gᵀ * fromBlocks 0 1 (-1) 0 * g = fromBlocks 0 1 (-1) 0) (u v : Fin 2 ⊕ Fin 2 → F) :
    spForm (g *ᵥ u) (g *ᵥ v) = spForm u v := by
  unfold spForm
  rw [mulVec_mulVec, ← vecMul_transpose g u, ← dotProduct_mulVec u gᵀ, mulVec_mulVec,
    ← Matrix.mul_assoc, hg]

theorem eq_zero_of_forall_spForm_eq_zero {u : Fin 2 ⊕ Fin 2 → F} (h : ∀ v, spForm u v = 0) :
    u = 0 := by
  have h0 := h (Pi.single (.inr 0) 1)
  have h1 := h (Pi.single (.inr 1) 1)
  have h2 := h (Pi.single (.inl 0) 1)
  have h3 := h (Pi.single (.inl 1) 1)
  simp [spForm_apply] at h0 h1 h2 h3
  funext k
  rcases k with i | i <;> fin_cases i
  · exact h0
  · exact h1
  · exact h2
  · exact h3

theorem transpose_mul_mul_apply_eq_spForm (P : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F)
    (k l : Fin 2 ⊕ Fin 2) :
    (Pᵀ * fromBlocks 0 1 (-1) 0 * P : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) k l =
      spForm (fun i => P i k) (fun i => P i l) := by
  rw [spForm_apply]
  simp [Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, one_apply]
  ring

end Form

section Basis

variable {F : Type} [Field F]

@[expose] def sp4ColMat (e f : Fin 2 → Fin 2 ⊕ Fin 2 → F) :
    Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F :=
  Matrix.of fun i k => Sum.elim e f k i

omit [Field F] in
theorem sp4ColMat_apply (e f : Fin 2 → Fin 2 ⊕ Fin 2 → F) (i k : Fin 2 ⊕ Fin 2) :
    sp4ColMat e f i k = Sum.elim e f k i :=
  rfl

theorem sp4ColMat_gram (e f : Fin 2 → Fin 2 ⊕ Fin 2 → F)
    (hef : ∀ i j, spForm (e i) (f j) = if i = j then 1 else 0)
    (hee : ∀ i j, spForm (e i) (e j) = 0) (hff : ∀ i j, spForm (f i) (f j) = 0) :
    (sp4ColMat e f)ᵀ * fromBlocks 0 1 (-1) 0 * sp4ColMat e f = fromBlocks 0 1 (-1) 0 := by
  ext k l
  rw [transpose_mul_mul_apply_eq_spForm]
  rcases k with i | i <;> rcases l with j | j
  · simp only [sp4ColMat_apply, Sum.elim_inl, fromBlocks_apply₁₁, Matrix.zero_apply]
    exact hee i j
  · simp only [sp4ColMat_apply, Sum.elim_inl, Sum.elim_inr, fromBlocks_apply₁₂, one_apply]
    exact hef i j
  · simp only [sp4ColMat_apply, Sum.elim_inl, Sum.elim_inr, fromBlocks_apply₂₁,
      Matrix.neg_apply, one_apply]
    rw [spForm_swap, hef j i]
    by_cases h : i = j
    · subst h
      simp
    · simp [h, Ne.symm h]
  · simp only [sp4ColMat_apply, Sum.elim_inr, fromBlocks_apply₂₂, Matrix.zero_apply]
    exact hff i j

theorem det_spJ_ne_zero :
    (fromBlocks 0 1 (-1) 0 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F).det ≠ 0 := by
  have h : (fromBlocks 0 1 (-1) 0 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *
      fromBlocks 0 (-1) 1 0 = 1 := by
    rw [fromBlocks_multiply]
    simp [fromBlocks_one]
  intro h0
  have h1 := congrArg Matrix.det h
  rw [det_mul, h0, zero_mul, det_one] at h1
  exact zero_ne_one h1

theorem det_ne_zero_of_gram {P : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F}
    (hP : Pᵀ * fromBlocks 0 1 (-1) 0 * P = fromBlocks 0 1 (-1) 0) : P.det ≠ 0 := by
  intro h0
  have h1 := congrArg Matrix.det hP
  rw [det_mul, det_mul, h0, mul_zero] at h1
  exact det_spJ_ne_zero h1.symm

theorem exists_eq_conj_of_colMat {x t : StatedSp 2 F} (e f : Fin 2 → Fin 2 ⊕ Fin 2 → F)
    (hef : ∀ i j, spForm (e i) (f j) = if i = j then 1 else 0)
    (hee : ∀ i j, spForm (e i) (e j) = 0) (hff : ∀ i j, spForm (f i) (f j) = 0)
    (hxt : ((x : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) * sp4ColMat e f =
      sp4ColMat e f * ((t : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F)) :
    ∃ g : StatedSp 2 F, x = g * t * g⁻¹ := by
  have hP := sp4ColMat_gram e f hef hee hff
  have hdet := det_ne_zero_of_gram hP
  set g : GL (Fin 2 ⊕ Fin 2) F := GeneralLinearGroup.mkOfDetNeZero (sp4ColMat e f) hdet with hg
  have hgS : g ∈ StatedSp 2 F := by
    rw [CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl.mem_statedSp_iff, hg,
      GeneralLinearGroup.val_mkOfDetNeZero]
    exact hP
  refine ⟨⟨g, hgS⟩, eq_mul_inv_of_mul_eq ?_⟩
  apply Subtype.ext
  apply Units.ext
  simp only [Subgroup.coe_mul, Units.val_mul, hg, GeneralLinearGroup.val_mkOfDetNeZero]
  exact hxt

end Basis

section TT

variable (F : Type) [Field F]

@[expose] noncomputable def sp4TT : StatedSp 2 F := sp4T F * sp4T' F

theorem coe_sp4TT :
    (((sp4TT F : StatedSp 2 F) : GL (Fin 2 ⊕ Fin 2) F) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) =
      CFSG.LieType.SteinbergBR.EvenSp.planeMat fun _ => ordThreeMat F := by
  change (((sp4T F : StatedSp 2 F) : GL (Fin 2 ⊕ Fin 2) F) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *
    (((sp4T' F : StatedSp 2 F) : GL (Fin 2 ⊕ Fin 2) F) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) = _
  rw [coe_sp4T, show (((sp4T' F : StatedSp 2 F) : GL (Fin 2 ⊕ Fin 2) F) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) = planeBlock 1 (ordThreeMat F) from
    coe_planeSp 1 _, planeBlock, planeBlock, CFSG.LieType.SteinbergBR.EvenSp.planeMat_mul]
  congr 1
  funext j
  fin_cases j <;> simp

theorem sp4TT_pow_three : sp4TT F ^ 3 = 1 := by
  rw [sp4TT, Commute.mul_pow (sp4T_commute F) 3, sp4T_pow_three, sp4T'_pow_three, one_mul]

end TT


section Order3

variable {F : Type} [Field F] [CharP F 2] {X : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F}

omit [CharP F 2] in
theorem mulVec_mulVec_mulVec_of_pow_three (hX3 : X ^ 3 = 1) (v : Fin 2 ⊕ Fin 2 → F) :
    X *ᵥ (X *ᵥ (X *ᵥ v)) = v := by
  have h : X * (X * X) = 1 := by rw [← hX3, pow_three]
  simp only [mulVec_mulVec, h, one_mulVec]

omit [CharP F 2] in
theorem sq_add_add_one_mulVec (v : Fin 2 ⊕ Fin 2 → F) :
    (X ^ 2 + X + 1) *ᵥ v = X *ᵥ (X *ᵥ v) + X *ᵥ v + v := by
  rw [add_mulVec, add_mulVec, one_mulVec, pow_two, mulVec_mulVec]

omit [CharP F 2] in
theorem mulVec_N (hX3 : X ^ 3 = 1) (v : Fin 2 ⊕ Fin 2 → F) :
    X *ᵥ (X *ᵥ (X *ᵥ v) + X *ᵥ v + v) = X *ᵥ (X *ᵥ v) + X *ᵥ v + v := by
  rw [mulVec_add, mulVec_add, mulVec_mulVec_mulVec_of_pow_three hX3]
  abel

omit [CharP F 2] in
theorem mulVec_M (v : Fin 2 ⊕ Fin 2 → F) :
    X *ᵥ (X *ᵥ v + v) = X *ᵥ (X *ᵥ v) + X *ᵥ v := by
  rw [mulVec_add]

theorem N_M (hX3 : X ^ 3 = 1) (v : Fin 2 ⊕ Fin 2 → F) :
    X *ᵥ (X *ᵥ (X *ᵥ v + v)) + X *ᵥ (X *ᵥ v + v) + (X *ᵥ v + v) = 0 := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  rw [mulVec_add, mulVec_add, mulVec_mulVec_mulVec_of_pow_three hX3]
  funext i
  simp only [Pi.add_apply, Pi.zero_apply]
  linear_combination (v i + (X *ᵥ (X *ᵥ v)) i + (X *ᵥ v) i) * h2

theorem N_add_M (v : Fin 2 ⊕ Fin 2 → F) :
    (X *ᵥ (X *ᵥ v) + X *ᵥ v + v) + (X *ᵥ (X *ᵥ v) + X *ᵥ v) = v := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  funext i
  simp only [Pi.add_apply]
  linear_combination ((X *ᵥ (X *ᵥ v)) i + (X *ᵥ v) i) * h2

theorem mulVec_mulVec_eq_of_N {v : Fin 2 ⊕ Fin 2 → F} (h : X *ᵥ (X *ᵥ v) + X *ᵥ v + v = 0) :
    X *ᵥ (X *ᵥ v) = X *ᵥ v + v := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  funext i
  have hi := congrFun h i
  simp only [Pi.add_apply, Pi.zero_apply] at hi ⊢
  linear_combination hi - ((X *ᵥ v) i + v i) * h2

theorem spForm_M_N (hX : Xᵀ * fromBlocks 0 1 (-1) 0 * X = fromBlocks 0 1 (-1) 0)
    (hX3 : X ^ 3 = 1) (z w : Fin 2 ⊕ Fin 2 → F) :
    spForm (X *ᵥ z + z) (X *ᵥ (X *ᵥ w) + X *ᵥ w + w) = 0 := by
  have h1 : spForm (X *ᵥ z) (X *ᵥ (X *ᵥ w) + X *ᵥ w + w) =
      spForm z (X *ᵥ (X *ᵥ w) + X *ᵥ w + w) := by
    conv_lhs => rw [← mulVec_N hX3 w]
    exact spForm_mulVec hX z _
  rw [spForm_add_left, h1, CharTwo.add_self_eq_zero]

theorem spForm_add_mulVec_add (hX : Xᵀ * fromBlocks 0 1 (-1) 0 * X = fromBlocks 0 1 (-1) 0)
    {v₀ v₁ : Fin 2 ⊕ Fin 2 → F} (h₀ : X *ᵥ (X *ᵥ v₀) = X *ᵥ v₀ + v₀) :
    spForm (v₀ + v₁) (X *ᵥ (v₀ + v₁)) =
      spForm v₀ (X *ᵥ v₀) + spForm v₁ (X *ᵥ v₁) + spForm v₀ v₁ := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have e1 : spForm v₁ (X *ᵥ v₀) = spForm v₁ v₀ + spForm (X *ᵥ v₁) v₀ := by
    rw [← spForm_mulVec hX v₁ (X *ᵥ v₀), h₀, spForm_add_right, spForm_mulVec hX]
  have s1 := spForm_swap v₀ (X *ᵥ v₁)
  have s2 := spForm_swap v₀ v₁
  rw [mulVec_add, spForm_add_left, spForm_add_right, spForm_add_right]
  linear_combination e1 + s1 + s2 - spForm v₀ v₁ * h2

omit [CharP F 2] in
theorem spForm_smul_mulVec_smul (c : F) (u : Fin 2 ⊕ Fin 2 → F) :
    spForm (c • u) (X *ᵥ (c • u)) = c * c * spForm u (X *ᵥ u) := by
  rw [mulVec_smul, spForm_smul_left, spForm_smul_right, mul_assoc]

theorem exists_spForm_smul_eq_one [Finite F] {u : Fin 2 ⊕ Fin 2 → F}
    (hu : spForm u (X *ᵥ u) ≠ 0) : ∃ c : F, spForm (c • u) (X *ᵥ (c • u)) = 1 := by
  obtain ⟨r, hr⟩ := isSquare_of_charTwo' (spForm u (X *ᵥ u))⁻¹
  refine ⟨r, ?_⟩
  rw [spForm_smul_mulVec_smul, ← hr, inv_mul_cancel₀ hu]

theorem spForm_mulVec_ne_zero_of_spForm_ne_zero
    (hX : Xᵀ * fromBlocks 0 1 (-1) 0 * X = fromBlocks 0 1 (-1) 0)
    {v₀ v₁ : Fin 2 ⊕ Fin 2 → F} (h₀ : X *ᵥ (X *ᵥ v₀) = X *ᵥ v₀ + v₀)
    (h01 : spForm v₀ v₁ ≠ 0) :
    spForm v₀ (X *ᵥ v₀) ≠ 0 ∨ spForm v₁ (X *ᵥ v₁) ≠ 0 ∨
      spForm (v₀ + v₁) (X *ᵥ (v₀ + v₁)) ≠ 0 := by
  by_contra h
  push Not at h
  obtain ⟨h1, h2, h3⟩ := h
  rw [spForm_add_mulVec_add hX h₀, h1, h2, zero_add, zero_add] at h3
  exact h01 h3

theorem exists_spForm_mulVec_eq_one [Finite F]
    (hX : Xᵀ * fromBlocks 0 1 (-1) 0 * X = fromBlocks 0 1 (-1) 0) (hX3 : X ^ 3 = 1)
    (hX1 : X ≠ 1) : ∃ z : Fin 2 ⊕ Fin 2 → F, spForm (X *ᵥ z + z) (X *ᵥ (X *ᵥ z + z)) = 1 := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  obtain ⟨z₀, hz₀⟩ : ∃ z₀ : Fin 2 ⊕ Fin 2 → F, X *ᵥ z₀ + z₀ ≠ 0 := by
    by_contra h
    push Not at h
    apply hX1
    rw [Matrix.ext_iff_mulVec]
    intro v
    rw [one_mulVec]
    funext i
    have hi := congrFun (h v) i
    simp only [Pi.add_apply, Pi.zero_apply] at hi
    linear_combination hi - v i * h2
  obtain ⟨w, hw⟩ : ∃ w, spForm (X *ᵥ z₀ + z₀) w ≠ 0 := by
    by_contra h
    push Not at h
    exact hz₀ (eq_zero_of_forall_spForm_eq_zero h)
  have hw' : spForm (X *ᵥ z₀ + z₀) (X *ᵥ (X *ᵥ w) + X *ᵥ w) ≠ 0 := by
    intro h0
    apply hw
    rw [← N_add_M w, spForm_add_right, spForm_M_N hX hX3, h0, add_zero]
  have hM : ∀ z : Fin 2 ⊕ Fin 2 → F,
      X *ᵥ (X *ᵥ (X *ᵥ z + z)) = X *ᵥ (X *ᵥ z + z) + (X *ᵥ z + z) := fun z =>
    mulVec_mulVec_eq_of_N (N_M hX3 z)
  have hrescale : ∀ z : Fin 2 ⊕ Fin 2 → F,
      spForm (X *ᵥ z + z) (X *ᵥ (X *ᵥ z + z)) ≠ 0 →
        ∃ z' : Fin 2 ⊕ Fin 2 → F, spForm (X *ᵥ z' + z') (X *ᵥ (X *ᵥ z' + z')) = 1 := by
    intro z hz
    obtain ⟨c, hc⟩ := exists_spForm_smul_eq_one hz
    refine ⟨c • z, ?_⟩
    rw [mulVec_smul, ← smul_add]
    exact hc
  rcases spForm_mulVec_ne_zero_of_spForm_ne_zero hX (hM z₀) hw' with h | h | h
  · exact hrescale z₀ h
  · exact hrescale (X *ᵥ w) h
  · have e : X *ᵥ (z₀ + X *ᵥ w) + (z₀ + X *ᵥ w) =
        (X *ᵥ z₀ + z₀) + (X *ᵥ (X *ᵥ w) + X *ᵥ w) := by
      rw [mulVec_add]
      abel
    apply hrescale (z₀ + X *ᵥ w)
    rw [e]
    exact h

end Order3


section Classes

variable {F : Type} [Field F]

theorem mul_colMat_apply (X : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F)
    (e f : Fin 2 → Fin 2 ⊕ Fin 2 → F) (i k : Fin 2 ⊕ Fin 2) :
    (X * sp4ColMat e f) i k = (X *ᵥ Sum.elim e f k) i := by
  simp [Matrix.mul_apply, mulVec, dotProduct, sp4ColMat_apply]

theorem sp4ColMat_mul_apply (T : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F)
    (e f : Fin 2 → Fin 2 ⊕ Fin 2 → F) (i k : Fin 2 ⊕ Fin 2) :
    (sp4ColMat e f * T) i k = ∑ l, T l k * Sum.elim e f l i := by
  simp only [Matrix.mul_apply, sp4ColMat_apply]
  exact Finset.sum_congr rfl fun l _ => mul_comm _ _

theorem gram_of_pairings {e₀ e₁ f₀ f₁ : Fin 2 ⊕ Fin 2 → F} (p1 : spForm e₀ f₀ = 1)
    (p2 : spForm e₁ f₁ = 1) (p3 : spForm e₀ e₁ = 0) (p4 : spForm e₀ f₁ = 0)
    (p5 : spForm f₀ e₁ = 0) (p6 : spForm f₀ f₁ = 0) :
    (∀ i j, spForm (![e₀, e₁] i) (![f₀, f₁] j) = if i = j then 1 else 0) ∧
      (∀ i j, spForm (![e₀, e₁] i) (![e₀, e₁] j) = 0) ∧
      ∀ i j, spForm (![f₀, f₁] i) (![f₀, f₁] j) = 0 := by
  refine ⟨fun i j => ?_, fun i j => ?_, fun i j => ?_⟩ <;> fin_cases i <;> fin_cases j <;>
    simp [p1, p2, p3, p4, p6, spForm_self]
  · rw [spForm_swap, p5, neg_zero]
  · rw [spForm_swap, p3, neg_zero]
  · rw [spForm_swap, p6, neg_zero]

variable [CharP F 2]

theorem exists_conj_eq_sp4T_of_basis {x : StatedSp 2 F} {e₀ e₁ f₀ f₁ : Fin 2 ⊕ Fin 2 → F}
    (p1 : spForm e₀ f₀ = 1) (p2 : spForm e₁ f₁ = 1) (p3 : spForm e₀ e₁ = 0)
    (p4 : spForm e₀ f₁ = 0) (p5 : spForm f₀ e₁ = 0) (p6 : spForm f₀ f₁ = 0)
    (a1 : ((x : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *ᵥ e₀ = f₀)
    (a2 : ((x : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *ᵥ f₀ =
      f₀ + e₀)
    (a3 : ((x : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *ᵥ e₁ = e₁)
    (a4 : ((x : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *ᵥ f₁ = f₁) :
    ∃ g : StatedSp 2 F, x = g * sp4T F * g⁻¹ := by
  obtain ⟨hef, hee, hff⟩ := gram_of_pairings p1 p2 p3 p4 p5 p6
  refine exists_eq_conj_of_colMat ![e₀, e₁] ![f₀, f₁] hef hee hff ?_
  rw [coe_sp4T]
  ext i k
  rw [mul_colMat_apply, sp4ColMat_mul_apply]
  rcases k with j | j <;> fin_cases j <;>
    simp [Fintype.sum_sum_type, Fin.sum_univ_two, planeBlock,
      CFSG.LieType.SteinbergBR.EvenSp.planeMat, ordThreeMat, a1, a2, a3, a4, CharTwo.neg_eq]
  all_goals ring

theorem exists_conj_eq_sp4TT_of_basis {x : StatedSp 2 F} {e₀ e₁ f₀ f₁ : Fin 2 ⊕ Fin 2 → F}
    (p1 : spForm e₀ f₀ = 1) (p2 : spForm e₁ f₁ = 1) (p3 : spForm e₀ e₁ = 0)
    (p4 : spForm e₀ f₁ = 0) (p5 : spForm f₀ e₁ = 0) (p6 : spForm f₀ f₁ = 0)
    (a1 : ((x : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *ᵥ e₀ = f₀)
    (a2 : ((x : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *ᵥ f₀ =
      f₀ + e₀)
    (a3 : ((x : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *ᵥ e₁ = f₁)
    (a4 : ((x : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *ᵥ f₁ =
      f₁ + e₁) :
    ∃ g : StatedSp 2 F, x = g * sp4TT F * g⁻¹ := by
  obtain ⟨hef, hee, hff⟩ := gram_of_pairings p1 p2 p3 p4 p5 p6
  refine exists_eq_conj_of_colMat ![e₀, e₁] ![f₀, f₁] hef hee hff ?_
  rw [coe_sp4TT]
  ext i k
  rw [mul_colMat_apply, sp4ColMat_mul_apply]
  rcases k with j | j <;> fin_cases j <;>
    simp [Fintype.sum_sum_type, Fin.sum_univ_two,
      CFSG.LieType.SteinbergBR.EvenSp.planeMat, ordThreeMat, a1, a2, a3, a4, CharTwo.neg_eq]
  all_goals ring

end Classes


section Conj

variable {F : Type} [Field F]

theorem coe_statedSp_pow_three {x : StatedSp 2 F} (hx3 : x ^ 3 = 1) :
    ((x : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) ^ 3 = 1 := by
  have h := congrArg (fun y : StatedSp 2 F =>
    ((y : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F)) hx3
  simpa using h

theorem coe_statedSp_ne_one {x : StatedSp 2 F} (hx1 : x ≠ 1) :
    ((x : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) ≠ 1 :=
  fun h => hx1 (Subtype.ext (Units.ext h))

variable [CharP F 2] [Finite F]

theorem exists_conj_eq_sp4T {x : StatedSp 2 F} (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1)
    (hN : ((x : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) ^ 2 +
      ((x : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) + 1 ≠ 0) :
    ∃ g : StatedSp 2 F, x = g * sp4T F * g⁻¹ := by
  have hX := CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl.mem_statedSp_iff.mp x.2
  have hX3 := coe_statedSp_pow_three hx3
  have hX1 := coe_statedSp_ne_one hx1
  generalize hXdef : ((x : GL (Fin 2 ⊕ Fin 2) F) :
    Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) = X at hX hX3 hX1 hN
  obtain ⟨z, hz⟩ := exists_spForm_mulVec_eq_one hX hX3 hX1
  obtain ⟨u, hu⟩ : ∃ u, X *ᵥ (X *ᵥ u) + X *ᵥ u + u ≠ 0 := by
    by_contra h
    push Not at h
    apply hN
    rw [Matrix.ext_iff_mulVec]
    intro v
    rw [sq_add_add_one_mulVec, h v, zero_mulVec]
  obtain ⟨w, hw⟩ : ∃ w, spForm (X *ᵥ (X *ᵥ u) + X *ᵥ u + u) w ≠ 0 := by
    by_contra h
    push Not at h
    exact hu (eq_zero_of_forall_spForm_eq_zero h)
  have hw' : spForm (X *ᵥ (X *ᵥ u) + X *ᵥ u + u) (X *ᵥ (X *ᵥ w) + X *ᵥ w + w) ≠ 0 := by
    intro h0
    apply hw
    rw [← N_add_M w, spForm_add_right, h0, zero_add, spForm_swap, spForm_M_N hX hX3, neg_zero]
  have p2 : spForm (X *ᵥ (X *ᵥ u) + X *ᵥ u + u)
      ((spForm (X *ᵥ (X *ᵥ u) + X *ᵥ u + u) (X *ᵥ (X *ᵥ w) + X *ᵥ w + w))⁻¹ •
        (X *ᵥ (X *ᵥ w) + X *ᵥ w + w)) = 1 := by
    rw [spForm_smul_right, inv_mul_cancel₀ hw']
  have p3 := spForm_M_N hX hX3 z u
  have p4 : spForm (X *ᵥ z + z)
      ((spForm (X *ᵥ (X *ᵥ u) + X *ᵥ u + u) (X *ᵥ (X *ᵥ w) + X *ᵥ w + w))⁻¹ •
        (X *ᵥ (X *ᵥ w) + X *ᵥ w + w)) = 0 := by
    rw [spForm_smul_right, spForm_M_N hX hX3 z w, mul_zero]
  have p5 : spForm (X *ᵥ (X *ᵥ z + z)) (X *ᵥ (X *ᵥ u) + X *ᵥ u + u) = 0 := by
    rw [mulVec_M]
    exact spForm_M_N hX hX3 (X *ᵥ z) u
  have p6 : spForm (X *ᵥ (X *ᵥ z + z))
      ((spForm (X *ᵥ (X *ᵥ u) + X *ᵥ u + u) (X *ᵥ (X *ᵥ w) + X *ᵥ w + w))⁻¹ •
        (X *ᵥ (X *ᵥ w) + X *ᵥ w + w)) = 0 := by
    rw [mulVec_M, spForm_smul_right, spForm_M_N hX hX3 (X *ᵥ z) w, mul_zero]
  have a2 := mulVec_mulVec_eq_of_N (N_M hX3 z)
  have a3 := mulVec_N hX3 u
  have a4 : X *ᵥ ((spForm (X *ᵥ (X *ᵥ u) + X *ᵥ u + u) (X *ᵥ (X *ᵥ w) + X *ᵥ w + w))⁻¹ •
        (X *ᵥ (X *ᵥ w) + X *ᵥ w + w)) =
      (spForm (X *ᵥ (X *ᵥ u) + X *ᵥ u + u) (X *ᵥ (X *ᵥ w) + X *ᵥ w + w))⁻¹ •
        (X *ᵥ (X *ᵥ w) + X *ᵥ w + w) := by
    rw [mulVec_smul, mulVec_N hX3 w]
  subst hXdef
  exact exists_conj_eq_sp4T_of_basis hz p2 p3 p4 p5 p6 rfl a2 a3 a4

theorem exists_conj_eq_sp4TT {x : StatedSp 2 F} (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1)
    (hN : ((x : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) ^ 2 +
      ((x : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) + 1 = 0) :
    ∃ g : StatedSp 2 F, x = g * sp4TT F * g⁻¹ := by
  have hX := CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl.mem_statedSp_iff.mp x.2
  have hX3 := coe_statedSp_pow_three hx3
  have hX1 := coe_statedSp_ne_one hx1
  generalize hXdef : ((x : GL (Fin 2 ⊕ Fin 2) F) :
    Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) = X at hX hX3 hX1 hN
  have hN' : ∀ v, X *ᵥ (X *ᵥ v) = X *ᵥ v + v := fun v =>
    mulVec_mulVec_eq_of_N (by rw [← sq_add_add_one_mulVec, hN, zero_mulVec])
  obtain ⟨z, hz⟩ := exists_spForm_mulVec_eq_one hX hX3 hX1
  obtain ⟨e₀, he₀⟩ : ∃ e₀, spForm e₀ (X *ᵥ e₀) = 1 := ⟨_, hz⟩
  have hfe : spForm (X *ᵥ e₀) e₀ = -1 := by rw [spForm_swap, he₀]
  have hπe : ∀ w, spForm (w - spForm w (X *ᵥ e₀) • e₀ + spForm w e₀ • (X *ᵥ e₀)) e₀ = 0 := by
    intro w
    rw [spForm_add_left, spForm_sub_left, spForm_smul_left, spForm_smul_left, spForm_self, hfe]
    ring
  have hπf : ∀ w, spForm (w - spForm w (X *ᵥ e₀) • e₀ + spForm w e₀ • (X *ᵥ e₀)) (X *ᵥ e₀) =
      0 := by
    intro w
    rw [spForm_add_left, spForm_sub_left, spForm_smul_left, spForm_smul_left, spForm_self, he₀]
    ring
  obtain ⟨u, w, huw⟩ : ∃ u w, spForm (u - spForm u (X *ᵥ e₀) • e₀ + spForm u e₀ • (X *ᵥ e₀))
      (w - spForm w (X *ᵥ e₀) • e₀ + spForm w e₀ • (X *ᵥ e₀)) ≠ 0 := by
    by_contra h
    push Not at h
    have h0 : ∀ u, u - spForm u (X *ᵥ e₀) • e₀ + spForm u e₀ • (X *ᵥ e₀) = 0 := fun u =>
      eq_zero_of_forall_spForm_eq_zero fun w => by
        have hw : w = (w - spForm w (X *ᵥ e₀) • e₀ + spForm w e₀ • (X *ᵥ e₀)) +
            spForm w (X *ᵥ e₀) • e₀ - spForm w e₀ • (X *ᵥ e₀) := by
          abel
        conv_lhs => rw [hw]
        rw [spForm_sub_right, spForm_add_right, spForm_smul_right, spForm_smul_right, h u w,
          hπe u, hπf u]
        ring
    have hone : (1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) =
        (Matrix.of fun i j => ![e₀ i, (X *ᵥ e₀) i] j : Matrix (Fin 2 ⊕ Fin 2) (Fin 2) F) *
          (Matrix.of fun j k => ![spForm (Pi.single k 1) (X *ᵥ e₀),
            -spForm (Pi.single k 1) e₀] j : Matrix (Fin 2) (Fin 2 ⊕ Fin 2) F) := by
      ext i k
      have hk := congrFun (h0 (Pi.single k 1)) i
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply,
        Pi.single_apply] at hk
      simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.one_apply]
      linear_combination hk
    have h1 := Matrix.rank_mul_le_left
      (Matrix.of fun i j => ![e₀ i, (X *ᵥ e₀) i] j : Matrix (Fin 2 ⊕ Fin 2) (Fin 2) F)
      (Matrix.of fun j k => ![spForm (Pi.single k 1) (X *ᵥ e₀),
        -spForm (Pi.single k 1) e₀] j : Matrix (Fin 2) (Fin 2 ⊕ Fin 2) F)
    rw [← hone, Matrix.rank_one] at h1
    have h2 := Matrix.rank_le_card_width
      (Matrix.of fun i j => ![e₀ i, (X *ᵥ e₀) i] j : Matrix (Fin 2 ⊕ Fin 2) (Fin 2) F)
    simp only [Fintype.card_sum, Fintype.card_fin] at h1 h2
    omega
  obtain ⟨v, hv, hve, hvf⟩ : ∃ v, spForm v (X *ᵥ v) ≠ 0 ∧ spForm v e₀ = 0 ∧
      spForm v (X *ᵥ e₀) = 0 := by
    rcases spForm_mulVec_ne_zero_of_spForm_ne_zero hX (hN' _) huw with h | h | h
    · exact ⟨_, h, hπe u, hπf u⟩
    · exact ⟨_, h, hπe w, hπf w⟩
    · exact ⟨_, h, by rw [spForm_add_left, hπe, hπe, add_zero],
        by rw [spForm_add_left, hπf, hπf, add_zero]⟩
  obtain ⟨c, hc⟩ := exists_spForm_smul_eq_one hv
  have hce : spForm (c • v) e₀ = 0 := by rw [spForm_smul_left, hve, mul_zero]
  have hcf : spForm (c • v) (X *ᵥ e₀) = 0 := by rw [spForm_smul_left, hvf, mul_zero]
  have p3 : spForm e₀ (c • v) = 0 := by rw [spForm_swap, hce, neg_zero]
  have p5 : spForm (X *ᵥ e₀) (c • v) = 0 := by rw [spForm_swap, hcf, neg_zero]
  have p4 : spForm e₀ (X *ᵥ (c • v)) = 0 := by
    have h1 : spForm e₀ (X *ᵥ (c • v)) = spForm (X *ᵥ (X *ᵥ e₀)) (c • v) := by
      conv_lhs => rw [← mulVec_mulVec_mulVec_of_pow_three hX3 e₀]
      exact spForm_mulVec hX _ _
    rw [h1, hN' e₀, spForm_add_left, p5, p3, add_zero]
  have p6 : spForm (X *ᵥ e₀) (X *ᵥ (c • v)) = 0 := by rw [spForm_mulVec hX, p3]
  subst hXdef
  exact exists_conj_eq_sp4TT_of_basis he₀ hc p3 p4 p5 p6 rfl (hN' e₀) rfl (hN' (c • v))

end Conj

end CFSG.RankThree.PartTwo.KFacts
