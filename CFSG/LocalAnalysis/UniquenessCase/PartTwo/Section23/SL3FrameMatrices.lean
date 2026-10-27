module

public import CFSG.ClassicalInvolution.ModelFacts.OddCover.SL3Basic
public import CFSG.ClassicalGroups.SpecialLinear.CyclicRootGroups

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.SL3Frame

open Matrix CFSG.ClassicalInvolution.ModelFacts.OddCover
open scoped MatrixGroups

variable {K : Type} [Field K]

@[expose] def rowGen (i : Fin 3) : Set (Matrix.SpecialLinearGroup (Fin 3) K) :=
  {g | ∃ (j : Fin 3) (hij : i ≠ j) (t : K),
    g = Matrix.SpecialLinearGroup.transvection hij t}

theorem rowGen_inv_mem {i : Fin 3} {g : Matrix.SpecialLinearGroup (Fin 3) K}
    (hg : g ∈ rowGen i) : g⁻¹ ∈ rowGen i := by
  obtain ⟨j, hij, t, rfl⟩ := hg
  exact ⟨j, hij, -t, by rw [Matrix.SpecialLinearGroup.transvection_inv]⟩

@[expose] def rowT (i : Fin 3) : Subgroup (Matrix.SpecialLinearGroup (Fin 3) K) :=
  Subgroup.mk (Submonoid.closure (rowGen i)) (by
    intro g hg
    induction hg using Submonoid.closure_induction with
    | mem x hx => exact Submonoid.subset_closure (rowGen_inv_mem hx)
    | one => simpa using Submonoid.one_mem (Submonoid.closure (rowGen i))
    | mul x y hx hy ihx ihy =>
        rw [_root_.mul_inv_rev]
        exact Submonoid.mul_mem _ ihy ihx)

theorem mem_rowT {i : Fin 3} {g : Matrix.SpecialLinearGroup (Fin 3) K} :
    g ∈ rowT i ↔ g ∈ Submonoid.closure (rowGen i) :=
  Subgroup.mem_mk _

theorem transvection_mem_rowT {i j : Fin 3} (hij : i ≠ j) (t : K) :
    Matrix.SpecialLinearGroup.transvection hij t ∈ rowT i := by
  rw [mem_rowT]
  exact Submonoid.subset_closure ⟨j, hij, t, rfl⟩

theorem rowT_row_eq_one {i : Fin 3} {g : Matrix.SpecialLinearGroup (Fin 3) K}
    (hg : g ∈ rowT i) {a : Fin 3} (ha : a ≠ i) :
    (g : Matrix (Fin 3) (Fin 3) K) a = (1 : Matrix (Fin 3) (Fin 3) K) a := by
  rw [mem_rowT] at hg
  induction hg using Submonoid.closure_induction with
  | mem x hx =>
      obtain ⟨j, hij, t, rfl⟩ := hx
      ext b
      rw [Matrix.SpecialLinearGroup.transvection_coe, Matrix.add_apply]
      have h1 : (Matrix.single i j t : Matrix (Fin 3) (Fin 3) K) a b = 0 := by
        rw [Matrix.single_apply, if_neg]
        exact fun h => ha h.1.symm
      rw [h1, add_zero]
  | one => ext b; simp
  | mul x y hx hy ihx ihy =>
      ext b
      rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, ihx,
        Finset.sum_eq_single a
          (by
            intro c _ hc
            rw [Matrix.one_apply, if_neg (Ne.symm hc), zero_mul])
          (by intro h; exact absurd (Finset.mem_univ a) h)]
      rw [Matrix.one_apply_eq, one_mul]
      exact congrFun ihy b

theorem rowT_apply_self_of_ne {i k : Fin 3} (hki : k ≠ i)
    {g : Matrix.SpecialLinearGroup (Fin 3) K} (hg : g ∈ rowT i) :
    (g : Matrix (Fin 3) (Fin 3) K) k k = 1 := by
  have h := congrFun (rowT_row_eq_one hg hki) k
  simpa using h

theorem rowT_inf_rowT_eq_bot {i j : Fin 3} (hij : i ≠ j) :
    (rowT i ⊓ rowT j : Subgroup (Matrix.SpecialLinearGroup (Fin 3) K)) = ⊥ := by
  rw [eq_bot_iff]
  intro g hg
  obtain ⟨hgi, hgj⟩ := Subgroup.mem_inf.mp hg
  rw [Subgroup.mem_bot]
  refine Subtype.ext (Matrix.ext fun a b => ?_)
  have hrow : (g : Matrix (Fin 3) (Fin 3) K) a = (1 : Matrix (Fin 3) (Fin 3) K) a := by
    by_cases hai : a = i
    · subst hai
      exact rowT_row_eq_one hgj hij
    · exact rowT_row_eq_one hgi hai
  exact congrFun hrow b

theorem iSup_rowT_eq_top :
    (⨆ i, rowT i : Subgroup (Matrix.SpecialLinearGroup (Fin 3) K)) = ⊤ := by
  refine CFSG.ClassicalGroups.SpecialLinear.eq_top_of_forall_transvection_mem
    (ι := Fin 3) (K := K) (⨆ i, rowT i) ?_
  intro i j hij t
  exact Subgroup.mem_iSup_of_mem i (transvection_mem_rowT hij t)

@[expose] def vecStab (i : Fin 3) : Subgroup (Matrix.SpecialLinearGroup (Fin 3) K) where
  carrier := {g | ∀ a : Fin 3,
    (g : Matrix (Fin 3) (Fin 3) K) a i = (1 : Matrix (Fin 3) (Fin 3) K) a i}
  one_mem' := by
    intro a
    rw [Matrix.SpecialLinearGroup.coe_one]
  mul_mem' := by
    intro g h hg hh a
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply,
      Finset.sum_eq_single i
        (by
          intro c _ hc
          rw [hh c, Matrix.one_apply, if_neg hc, mul_zero])
        (by intro hmem; exact absurd (Finset.mem_univ i) hmem)]
    rw [hh i, Matrix.one_apply_eq, mul_one, hg a]
  inv_mem' := by
    intro g hg a
    have hmul : ((g⁻¹ * g : Matrix.SpecialLinearGroup (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K) a i = (1 : Matrix (Fin 3) (Fin 3) K) a i := by
      rw [inv_mul_cancel g, Matrix.SpecialLinearGroup.coe_one]
    have hsum : ((g⁻¹ * g : Matrix.SpecialLinearGroup (Fin 3) K) :
          Matrix (Fin 3) (Fin 3) K) a i =
        (((g⁻¹ : Matrix.SpecialLinearGroup (Fin 3) K)) :
          Matrix (Fin 3) (Fin 3) K) a i := by
      rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply,
        Finset.sum_eq_single i
          (by
            intro c _ hc
            rw [hg c, Matrix.one_apply, if_neg hc, mul_zero])
          (by intro hmem; exact absurd (Finset.mem_univ i) hmem)]
      rw [hg i, Matrix.one_apply_eq, mul_one]
    rw [hsum] at hmul
    exact hmul

theorem mem_vecStab {i : Fin 3} {g : Matrix.SpecialLinearGroup (Fin 3) K} :
    g ∈ vecStab i ↔
      (g : Matrix (Fin 3) (Fin 3) K) *ᵥ (Pi.single i (1 : K) : Fin 3 → K) =
        Pi.single i 1 := by
  constructor
  · intro hg
    rw [Matrix.mulVec_single_one]
    funext a
    rw [Matrix.col_apply]
    simpa [Pi.single_apply, Matrix.one_apply] using hg a
  · intro hg a
    have h := congrFun hg a
    rw [Matrix.mulVec_single_one, Matrix.col_apply] at h
    simpa [Pi.single_apply, Matrix.one_apply] using h

theorem transvection_mulVec_single_of_ne {i j l : Fin 3} (hij : i ≠ j)
    (hli : l ≠ i) (hlj : l ≠ j) (t : K) :
    (Matrix.SpecialLinearGroup.transvection hij t : Matrix (Fin 3) (Fin 3) K) *ᵥ
      (Pi.single l (1 : K) : Fin 3 → K) = Pi.single l 1 := by
  rw [Matrix.SpecialLinearGroup.transvection_coe, Matrix.add_mulVec, Matrix.one_mulVec,
    Matrix.single_mulVec_eq]
  have h : (Pi.single l (1 : K) : Fin 3 → K) j = 0 := by
    rw [Pi.single_eq_of_ne (Ne.symm hlj)]
  rw [h, mul_zero, zero_smul, add_zero]

theorem transvection_mem_vecStab {i j l : Fin 3} (hjl : j ≠ l) (hij : i ≠ j) (hil : i ≠ l)
    (t : K) :
    Matrix.SpecialLinearGroup.transvection hjl t ∈ vecStab i := by
  intro a
  have hcol : (Matrix.SpecialLinearGroup.transvection hjl t :
        Matrix (Fin 3) (Fin 3) K).col i = Pi.single i 1 := by
    rw [← Matrix.mulVec_single_one]
    exact transvection_mulVec_single_of_ne hjl hij hil t
  have h := congrFun hcol a
  rw [Matrix.col_apply] at h
  simpa [Pi.single_apply, Matrix.one_apply] using h

@[expose] def rowProd (i j : Fin 3) (hij : i ≠ j) (a : K) :
    Matrix.SpecialLinearGroup (Fin 3) K :=
  Matrix.SpecialLinearGroup.transvection hij 1 *
    Matrix.SpecialLinearGroup.transvection hij.symm (a - 1) *
    Matrix.SpecialLinearGroup.transvection hij (-a⁻¹) *
    Matrix.SpecialLinearGroup.transvection hij.symm (a - a ^ 2)

theorem rowProd_eq_diag2n {i j : Fin 3} (hij : i ≠ j) {a : K} (ha : a ≠ 0) :
    rowProd i j hij a = Matrix.SpecialLinearGroup.diag2n hij a ha := by
  rw [rowProd, CFSG.ClassicalGroups.SpecialLinear.diag2n_eq_transvection_prod hij ha]

theorem rowProd_coe {i j : Fin 3} (hij : i ≠ j) {a : K} (ha : a ≠ 0) :
    (rowProd i j hij a : Matrix (Fin 3) (Fin 3) K) =
      Matrix.diagonal (fun l => if l = i then a else if l = j then a⁻¹ else 1) := by
  rw [rowProd_eq_diag2n hij ha]
  exact Matrix.SpecialLinearGroup.diag2n_coe hij a ha

theorem rowProd_mem_rowT_sup {i j : Fin 3} (hij : i ≠ j) (a : K) :
    rowProd i j hij a ∈ rowT i ⊔ rowT j := by
  rw [rowProd]
  have h1 : Matrix.SpecialLinearGroup.transvection hij (1 : K) ∈ rowT i ⊔ rowT j :=
    Subgroup.mem_sup_left (transvection_mem_rowT hij 1)
  have h2 : Matrix.SpecialLinearGroup.transvection hij.symm (a - 1) ∈ rowT i ⊔ rowT j :=
    Subgroup.mem_sup_right (transvection_mem_rowT hij.symm (a - 1))
  have h3 : Matrix.SpecialLinearGroup.transvection hij (-a⁻¹) ∈ rowT i ⊔ rowT j :=
    Subgroup.mem_sup_left (transvection_mem_rowT hij (-a⁻¹))
  have h4 : Matrix.SpecialLinearGroup.transvection hij.symm (a - a ^ 2) ∈ rowT i ⊔ rowT j :=
    Subgroup.mem_sup_right (transvection_mem_rowT hij.symm (a - a ^ 2))
  exact (rowT i ⊔ rowT j).mul_mem ((rowT i ⊔ rowT j).mul_mem
    ((rowT i ⊔ rowT j).mul_mem h1 h2) h3) h4

@[expose] def kappa (i j : Fin 3) (hij : i ≠ j) (t : Fin 3 → K)
    (D : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix.SpecialLinearGroup (Fin 3) K :=
  (rowProd i j hij (t i))⁻¹ * D

private theorem diagonal_entries_ne_zero {t : Fin 3 → K}
    {D : Matrix.SpecialLinearGroup (Fin 3) K}
    (hD : (D : Matrix (Fin 3) (Fin 3) K) = Matrix.diagonal t) : ∀ l, t l ≠ 0 := by
  have hprod : ∏ l, t l = 1 := by
    have h := D.2
    rwa [hD, Matrix.det_diagonal] at h
  intro l hl
  have hzero : ∏ l, t l = 0 := Finset.prod_eq_zero (Finset.mem_univ l) hl
  rw [hprod] at hzero
  exact one_ne_zero hzero

private theorem eq_diagonal_of_diagonal_mul {d t : Fin 3 → K} (hd : ∀ l, d l ≠ 0)
    {κ : Matrix (Fin 3) (Fin 3) K}
    (h : ∀ l m, d l * κ l m = if l = m then t l else 0) :
    κ = Matrix.diagonal (fun r => (d r)⁻¹ * t r) := by
  ext l m
  by_cases hlm : l = m
  · have hh : d l * κ l m = t l := by rw [h, if_pos hlm]
    rw [hlm] at hh ⊢
    rw [Matrix.diagonal_apply_eq]
    change κ m m = (d m)⁻¹ * t m
    rw [← hh, ← mul_assoc, inv_mul_cancel₀ (hd m), one_mul]
  · have hh : d l * κ l m = 0 := by rw [h, if_neg hlm]
    rw [Matrix.diagonal_apply_ne (fun r => (d r)⁻¹ * t r) (i := l) (j := m) hlm]
    exact (mul_eq_zero.mp hh).resolve_left (hd l)

private theorem diag2n_ne_zero {i j : Fin 3} {t : Fin 3 → K} (hti : t i ≠ 0) :
    ∀ l, (if l = i then t i else if l = j then (t i)⁻¹ else 1) ≠ 0 := by
  intro l
  by_cases hli : l = i
  · subst hli
    simpa using hti
  · by_cases hlj : l = j
    · subst hlj
      simpa [hli] using inv_ne_zero hti
    · simp [hli, hlj]

private theorem inv_mul_diag2n_eq {i j : Fin 3} (hij : i ≠ j) {t : Fin 3 → K}
    (hti : t i ≠ 0) (l : Fin 3) :
    ((if l = i then t i else if l = j then (t i)⁻¹ else 1))⁻¹ * t l =
      if l = i then 1 else if l = j then t i * t j else t l := by
  by_cases hli : l = i
  · subst hli
    simp [hij, hti]
  · by_cases hlj : l = j
    · subst hlj
      simp [hli, hti]
    · simp [hli, hlj]

theorem kappa_coe {i j : Fin 3} (hij : i ≠ j) {t : Fin 3 → K}
    {D : Matrix.SpecialLinearGroup (Fin 3) K}
    (hD : (D : Matrix (Fin 3) (Fin 3) K) = Matrix.diagonal t) :
    (kappa i j hij t D : Matrix (Fin 3) (Fin 3) K) =
      Matrix.diagonal (fun l => if l = i then 1 else if l = j then t i * t j else t l) := by
  have ht0 : ∀ l, t l ≠ 0 := diagonal_entries_ne_zero hD
  have hti : t i ≠ 0 := ht0 i
  have hy : ((rowProd i j hij (t i) : Matrix.SpecialLinearGroup (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K) =
      Matrix.diagonal (fun l => if l = i then t i else if l = j then (t i)⁻¹ else 1) :=
    rowProd_coe hij hti
  have hd0 : ∀ l, (if l = i then t i else if l = j then (t i)⁻¹ else 1) ≠ 0 :=
    diag2n_ne_zero hti
  have hmul : ((rowProd i j hij (t i) : Matrix.SpecialLinearGroup (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K) *
      (kappa i j hij t D : Matrix (Fin 3) (Fin 3) K) = (D : Matrix (Fin 3) (Fin 3) K) := by
    have hEq : rowProd i j hij (t i) * kappa i j hij t D = D := by
      rw [kappa]
      group
    rw [← Matrix.SpecialLinearGroup.coe_mul, hEq]
  have h : ∀ l m,
      (if l = i then t i else if l = j then (t i)⁻¹ else 1) *
        (kappa i j hij t D : Matrix (Fin 3) (Fin 3) K) l m =
      if l = m then t l else 0 := by
    intro l m
    have h' := congrFun (congrFun hmul l) m
    rwa [hy, Matrix.diagonal_mul, hD, Matrix.diagonal_apply] at h'
  rw [eq_diagonal_of_diagonal_mul hd0 h]
  congr 1
  exact funext (inv_mul_diag2n_eq hij hti)

theorem kappa_not_mem_rowT {i j k : Fin 3} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    {t : Fin 3 → K} {D : Matrix.SpecialLinearGroup (Fin 3) K}
    (hD : (D : Matrix (Fin 3) (Fin 3) K) = Matrix.diagonal t) (htk : t k ≠ 1) :
    kappa i j hij t D ∉ rowT i := by
  intro hmem
  have hkk : (kappa i j hij t D : Matrix (Fin 3) (Fin 3) K) k k = 1 :=
    rowT_apply_self_of_ne hik.symm hmem
  rw [kappa_coe hij hD, Matrix.diagonal_apply_eq] at hkk
  rw [if_neg hik.symm, if_neg hjk.symm] at hkk
  exact htk hkk

theorem kappa_pow_card_sub_one [Fintype K] {i j : Fin 3} (hij : i ≠ j) {t : Fin 3 → K}
    {D : Matrix.SpecialLinearGroup (Fin 3) K}
    (hD : (D : Matrix (Fin 3) (Fin 3) K) = Matrix.diagonal t) :
    kappa i j hij t D ^ (Nat.card K - 1) = 1 := by
  have ht0 : ∀ l, t l ≠ 0 := diagonal_entries_ne_zero hD
  have hti : t i ≠ 0 := ht0 i
  have hdκ0 : ∀ l, (if l = i then 1 else if l = j then t i * t j else t l) ≠ 0 := by
    intro l
    by_cases hli : l = i
    · subst hli
      simp
    · by_cases hlj : l = j
      · rw [hlj] at hli ⊢
        simpa [hli] using mul_ne_zero hti (ht0 j)
      · simpa [hli, hlj] using ht0 l
  refine Subtype.ext ?_
  rw [Matrix.SpecialLinearGroup.coe_pow, kappa_coe hij hD, Matrix.diagonal_pow]
  have hpow : (fun l => if l = i then 1 else if l = j then t i * t j else t l) ^
      (Nat.card K - 1) = fun _ => 1 := by
    funext l
    rw [Nat.card_eq_fintype_card]
    change (if l = i then 1 else if l = j then t i * t j else t l) ^
      (Fintype.card K - 1) = 1
    exact FiniteField.pow_card_sub_one_eq_one _ (hdκ0 l)
  rw [hpow, Matrix.diagonal_one, Matrix.SpecialLinearGroup.coe_one]

theorem diagonal_eq_rowProd_mul_kappa {i j : Fin 3} (hij : i ≠ j) {t : Fin 3 → K}
    {D : Matrix.SpecialLinearGroup (Fin 3) K}
    (hD : (D : Matrix (Fin 3) (Fin 3) K) = Matrix.diagonal t) :
    D = rowProd i j hij (t i) * kappa i j hij t D := by
  rw [kappa]
  group

section CharTwo

variable [CharP K 2]

private theorem uSL_mul_tSL_conj {c : K} (hc0 : c ≠ 0) (hden : 1 + c ^ 3 ≠ 0) (a b : K) :
    uSL (a / (1 + c ^ 3)) (b / (1 + c ^ 3)) 0 *
      uSL ((c ^ 3)⁻¹ * a) ((c ^ 3)⁻¹ * b) 0 =
    tSL ((Units.mk0 c hc0)⁻¹ * (Units.mk0 c hc0)⁻¹, Units.mk0 c hc0) *
      uSL (a / (1 + c ^ 3)) (b / (1 + c ^ 3)) 0 *
      (tSL ((Units.mk0 c hc0)⁻¹ * (Units.mk0 c hc0)⁻¹, Units.mk0 c hc0))⁻¹ := by
  have hconj : tSL ((Units.mk0 c hc0)⁻¹ * (Units.mk0 c hc0)⁻¹, Units.mk0 c hc0) *
        uSL (a / (1 + c ^ 3)) (b / (1 + c ^ 3)) 0 *
        (tSL ((Units.mk0 c hc0)⁻¹ * (Units.mk0 c hc0)⁻¹, Units.mk0 c hc0))⁻¹ =
      uSL ((c ^ 3)⁻¹ * (a / (1 + c ^ 3))) ((c ^ 3)⁻¹ * (b / (1 + c ^ 3))) 0 := by
    simp only [tSL_conj_uSL, Units.val_mul, Units.val_inv_eq_inv_val, Units.val_mk0]
    congr 2 <;> field_simp [hc0, hden] <;> ring
  rw [hconj]
  simp only [uSL_mul, mul_zero, add_zero]
  congr 2
  · field_simp [hc0, hden]
    rw [show c ^ 3 + (1 + c ^ 3) = 1 by
      rw [show c ^ 3 + (1 + c ^ 3) = 1 + 2 * c ^ 3 by ring]
      rw [show (2 : K) = 0 from CharTwo.two_eq_zero]
      ring]
    ring
  · field_simp [hc0, hden]
    rw [show c ^ 3 + (1 + c ^ 3) = 1 by
      rw [show c ^ 3 + (1 + c ^ 3) = 1 + 2 * c ^ 3 by ring]
      rw [show (2 : K) = 0 from CharTwo.two_eq_zero]
      ring]
    ring

theorem conj_tSL_mul_uSL {c : K} (hc0 : c ≠ 0) (hc3 : c ^ 3 ≠ 1) (a b : K) :
    uSL (a / (1 + c ^ 3)) (b / (1 + c ^ 3)) 0 *
      (tSL ((Units.mk0 c hc0)⁻¹ * (Units.mk0 c hc0)⁻¹, Units.mk0 c hc0) * uSL a b 0) *
      (uSL (a / (1 + c ^ 3)) (b / (1 + c ^ 3)) 0)⁻¹ =
    tSL ((Units.mk0 c hc0)⁻¹ * (Units.mk0 c hc0)⁻¹, Units.mk0 c hc0) := by
  let T : Matrix.SpecialLinearGroup (Fin 3) K :=
    tSL ((Units.mk0 c hc0)⁻¹ * (Units.mk0 c hc0)⁻¹, Units.mk0 c hc0)
  let B : Matrix.SpecialLinearGroup (Fin 3) K := uSL a b 0
  let N : Matrix.SpecialLinearGroup (Fin 3) K :=
    uSL (a / (1 + c ^ 3)) (b / (1 + c ^ 3)) 0
  have hden : (1 + c ^ 3) ≠ 0 := by
    intro h
    apply hc3
    have h' : c ^ 3 = -1 := eq_neg_of_add_eq_zero_right h
    rwa [CharTwo.neg_eq] at h'
  have hTconj : T * B * T⁻¹ = uSL ((c ^ 3)⁻¹ * a) ((c ^ 3)⁻¹ * b) 0 := by
    simp only [T, B, tSL_conj_uSL, Units.val_mul, Units.val_inv_eq_inv_val, Units.val_mk0]
    congr 2 <;> field_simp [hc0] <;> ring
  have hTB : T * B = uSL ((c ^ 3)⁻¹ * a) ((c ^ 3)⁻¹ * b) 0 * T := by
    rw [← hTconj]
    group
  have hNB : N * uSL ((c ^ 3)⁻¹ * a) ((c ^ 3)⁻¹ * b) 0 = T * N * T⁻¹ := by
    simpa [T, N] using uSL_mul_tSL_conj hc0 hden a b
  have hmain : N * (T * B) * N⁻¹ = T := by
    calc N * (T * B) * N⁻¹
        = N * (uSL ((c ^ 3)⁻¹ * a) ((c ^ 3)⁻¹ * b) 0 * T) * N⁻¹ := by rw [hTB]
      _ = (N * uSL ((c ^ 3)⁻¹ * a) ((c ^ 3)⁻¹ * b) 0) * T * N⁻¹ := by group
      _ = (T * N * T⁻¹) * T * N⁻¹ := by rw [hNB]
      _ = T := by group
  simpa [T, N, B] using hmain

end CharTwo
