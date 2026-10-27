module

public import CFSG.RankThree.CentralLiftSO.SymplecticTorusWeyl
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticFlagOrder
public import CFSG.RankThree.CentralLift.LinearRootRelations
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplitEta

public section

namespace CFSG.RankThree.CentralLiftSO.Sp

open Matrix CFSG.Assembly.LowTwoRank CFSG.LieType.CentralExt CFSG.RankThree.CentralLift
open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (unipotent borelSubgroup flagOrder
  flagOrder_inl flagOrder_inr mem_unipotent_iff_reindex blockMat IsUnitriangular
  unipotent_subgroupOf_borelSubgroup_normal unipotent_le_borelSubgroup torus_le_borelSubgroup
  diagHom coe_diagHom_apply ker_diagHom card_unipotent)
open CFSG.LieType.Chevalley (uSL vSL coe_uSL coe_vSL)
open CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit (pairMat_upper pairMat_lower)
open CFSG.RankThree.CentralLift.LinearRoots (uSL_add uSL_zero)

section Matrices

variable {r : ℕ} {k : Type} [Field k]

theorem conj_apply_of_isLinePerm {ι : Type*} [Fintype ι] [DecidableEq ι] {g : GL ι k}
    {σ : Equiv.Perm ι} (hg : IsLinePerm σ (g : Matrix ι ι k)) (X : Matrix ι ι k) (a b : ι) :
    ((g : Matrix ι ι k) * X * ((g⁻¹ : GL ι k) : Matrix ι ι k)) (σ a) (σ b) =
      (g : Matrix ι ι k) (σ a) a * X a b * ((g : Matrix ι ι k) (σ b) b)⁻¹ := by
  have hginv := hg.inv
  have h1 : ((g⁻¹ : GL ι k) : Matrix ι ι k) b (σ b) = ((g : Matrix ι ι k) (σ b) b)⁻¹ := by
    have hmul : (((g⁻¹ : GL ι k) : Matrix ι ι k) * (g : Matrix ι ι k)) b b = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one, one_apply_eq]
    rw [mul_apply, Finset.sum_eq_single (σ b)] at hmul
    · exact eq_inv_of_mul_eq_one_left hmul
    · intro c _ hc
      rw [hg.apply_eq_zero (x := b) (y := c) hc, mul_zero]
    · simp
  rw [mul_apply, Finset.sum_eq_single b]
  · rw [mul_apply, Finset.sum_eq_single a, h1]
    · intro c _ hca
      rw [hg.apply_eq_zero (x := c) (y := σ a) (fun h => hca (σ.injective h).symm), zero_mul]
    · simp
  · intro d _ hdb
    rw [hginv.apply_eq_zero (x := σ b) (y := d) (by simpa using hdb), mul_zero]
  · simp

theorem flagOrder_swap (c : Fin r ⊕ Fin r) :
    (flagOrder r c.swap : ℕ) = 2 * r - 1 - flagOrder r c := by
  rcases c with i | i
  · rw [Sum.swap_inl, flagOrder_inr, flagOrder_inl]
    have := i.isLt
    omega
  · rw [Sum.swap_inr, flagOrder_inl, flagOrder_inr]
    have := i.isLt
    omega

theorem flagOrder_lt (c : Fin r ⊕ Fin r) : (flagOrder r c : ℕ) < 2 * r := (flagOrder r c).isLt

theorem mem_unipotent_iff_flag {g : StatedSp r k} :
    g ∈ unipotent r k ↔
      (∀ x y : Fin r ⊕ Fin r, (flagOrder r y : ℕ) < flagOrder r x →
        ((g : GL (Fin r ⊕ Fin r) k) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) k) x y = 0) ∧
      ∀ x, ((g : GL (Fin r ⊕ Fin r) k) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) k) x x = 1 := by
  rw [mem_unipotent_iff_reindex]
  simp only [Matrix.IsUpperTriangular, Matrix.BlockTriangular, reindex_apply, submatrix_apply,
    id]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun x y hxy => ?_, fun x => ?_⟩
    · have := h1 (i := flagOrder r x) (j := flagOrder r y) (Fin.lt_def.2 hxy)
      simpa using this
    · simpa using h2 (flagOrder r x)
  · rintro ⟨h1, h2⟩
    refine ⟨fun a b hab => h1 _ _ (by simpa using Fin.lt_def.1 hab), fun a => h2 _⟩

theorem conj_mem_unipotent {g X : StatedSp r k} {σ : Equiv.Perm (Fin r ⊕ Fin r)}
    (hg : IsLinePerm σ ((g : GL (Fin r ⊕ Fin r) k) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) k))
    (hdiag : ∀ x, ((X : GL (Fin r ⊕ Fin r) k) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) k) x x = 1)
    (hX : ∀ x y, x ≠ y →
      ((X : GL (Fin r ⊕ Fin r) k) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) k) x y ≠ 0 →
        (flagOrder r (σ x) : ℕ) < flagOrder r (σ y)) :
    g * X * g⁻¹ ∈ unipotent r k := by
  rw [mem_unipotent_iff_flag]
  have hconj : ∀ a b, ((((g * X * g⁻¹ : StatedSp r k) : GL (Fin r ⊕ Fin r) k)) :
      Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) k) (σ a) (σ b) =
      ((g : GL (Fin r ⊕ Fin r) k) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) k) (σ a) a *
        ((X : GL (Fin r ⊕ Fin r) k) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) k) a b *
        (((g : GL (Fin r ⊕ Fin r) k) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) k) (σ b) b)⁻¹ := by
    intro a b
    rw [← conj_apply_of_isLinePerm hg]
    rfl
  refine ⟨fun x y hxy => ?_, fun x => ?_⟩
  · obtain ⟨a, rfl⟩ := σ.surjective x
    obtain ⟨b, rfl⟩ := σ.surjective y
    rw [hconj]
    have hab : a ≠ b := by
      rintro rfl
      exact lt_irrefl _ hxy
    by_cases h0 : ((X : GL (Fin r ⊕ Fin r) k) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) k) a b = 0
    · rw [h0, mul_zero, zero_mul]
    · exact absurd (hX a b hab h0) (not_lt.2 hxy.le)
  · obtain ⟨a, rfl⟩ := σ.surjective x
    rw [hconj, hdiag, mul_one, mul_inv_cancel₀ (hg.apply_ne_zero a)]

end Matrices

section Simple

variable {r : ℕ} {k : Type} [Field k]

@[expose] def simplePos (i : Fin r) : (Fin r ⊕ Fin r) × (Fin r ⊕ Fin r) :=
  if h : i.val + 1 < r then (Sum.inl i, Sum.inl ⟨i.val + 1, h⟩) else (Sum.inl i, Sum.inr i)

theorem simplePos_of_lt {i : Fin r} (h : i.val + 1 < r) :
    simplePos i = (Sum.inl i, Sum.inl ⟨i.val + 1, h⟩) :=
  dite_eq_left h

theorem simplePos_of_not_lt {i : Fin r} (h : ¬i.val + 1 < r) :
    simplePos i = (Sum.inl i, Sum.inr i) :=
  dite_eq_right h

theorem flagOrder_simplePos (i : Fin r) :
    (flagOrder r (simplePos i).2 : ℕ) = flagOrder r (simplePos i).1 + 1 := by
  by_cases h : i.val + 1 < r
  · rw [simplePos_of_lt h, flagOrder_inl, flagOrder_inl]
  · rw [simplePos_of_not_lt h, flagOrder_inr, flagOrder_inl]
    have := i.isLt
    omega

theorem flagOrder_injective_val {a b : Fin r ⊕ Fin r}
    (h : (flagOrder r a : ℕ) = flagOrder r b) : a = b :=
  (flagOrder r).injective (Fin.ext h)

theorem mul_apply_of_adjacent {g h : StatedSp r k} (hg : g ∈ unipotent r k)
    (hh : h ∈ unipotent r k) {a b : Fin r ⊕ Fin r}
    (hab : (flagOrder r b : ℕ) = flagOrder r a + 1) :
    (((g * h : StatedSp r k) : GL (Fin r ⊕ Fin r) k) :
      Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) k) a b =
      ((g : GL (Fin r ⊕ Fin r) k) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) k) a b +
        ((h : GL (Fin r ⊕ Fin r) k) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) k) a b := by
  obtain ⟨hg1, hg2⟩ := mem_unipotent_iff_flag.1 hg
  obtain ⟨hh1, hh2⟩ := mem_unipotent_iff_flag.1 hh
  have hne : a ≠ b := fun e => by rw [e] at hab; omega
  rw [Subgroup.coe_mul, Units.val_mul, mul_apply, Finset.sum_eq_add a b hne]
  · rw [hg2, one_mul, hh2, mul_one, add_comm]
  · intro c _ hc
    have hfo : (flagOrder r c : ℕ) ≠ flagOrder r a := fun e => hc.1 (flagOrder_injective_val e)
    have hfo' : (flagOrder r c : ℕ) ≠ flagOrder r b := fun e => hc.2 (flagOrder_injective_val e)
    rcases Nat.lt_or_gt_of_ne hfo with h1 | h1
    · rw [hg1 a c h1, zero_mul]
    · rw [hh1 c b (by omega), mul_zero]
  · simp
  · simp

theorem inv_apply_of_adjacent {g : StatedSp r k} (hg : g ∈ unipotent r k) {a b : Fin r ⊕ Fin r}
    (hab : (flagOrder r b : ℕ) = flagOrder r a + 1) :
    (((g⁻¹ : StatedSp r k) : GL (Fin r ⊕ Fin r) k) :
      Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) k) a b =
      -((g : GL (Fin r ⊕ Fin r) k) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) k) a b := by
  have hne : a ≠ b := fun e => by rw [e] at hab; omega
  have h := mul_apply_of_adjacent hg (inv_mem hg) hab
  rw [mul_inv_cancel, OneMemClass.coe_one, Units.val_one, one_apply_ne hne] at h
  linear_combination -h

theorem mul_apply_last {A : Matrix (Fin r) (Fin r) k} (hA : IsUnitriangular A)
    (C : Matrix (Fin r) (Fin r) k) {i : Fin r} (h : ¬i.val + 1 < r) : (A * C) i i = C i i := by
  rw [mul_apply, Finset.sum_eq_single i]
  · rw [hA.2 i, one_mul]
  · intro j _ hji
    have hlt : j < i := by
      rcases lt_or_gt_of_ne hji with h' | h'
      · exact h'
      · exact absurd (Fin.lt_def.1 h') (by have := j.isLt; omega)
    rw [hA.1 hlt, zero_mul]
  · simp

theorem simpleCond_iff {g : StatedSp r k} {i : Fin r} :
    (∃ A C : Matrix (Fin r) (Fin r) k, IsUnitriangular A ∧ Cᵀ = C ∧
      ((g : GL (Fin r ⊕ Fin r) k) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) k) = blockMat A C ∧
      if h : i.val + 1 < r then A i ⟨i.val + 1, h⟩ = 0 else C i i = 0) ↔
      g ∈ unipotent r k ∧ ((g : GL (Fin r ⊕ Fin r) k) :
        Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) k) (simplePos i).1 (simplePos i).2 = 0 := by
  constructor
  · rintro ⟨A, C, hA, hC, hg, hcond⟩
    refine ⟨⟨A, C, hA, hC, hg⟩, ?_⟩
    rw [hg]
    by_cases h : i.val + 1 < r
    · rw [dite_eq_left h] at hcond
      rw [simplePos_of_lt h, blockMat, fromBlocks_apply₁₁]
      exact hcond
    · rw [dite_eq_right h] at hcond
      rw [simplePos_of_not_lt h, blockMat, fromBlocks_apply₁₂, mul_apply_last hA C h]
      exact hcond
  · rintro ⟨⟨A, C, hA, hC, hg⟩, h0⟩
    refine ⟨A, C, hA, hC, hg, ?_⟩
    rw [hg] at h0
    by_cases h : i.val + 1 < r
    · rw [dite_eq_left h]
      rw [simplePos_of_lt h, blockMat, fromBlocks_apply₁₁] at h0
      exact h0
    · rw [dite_eq_right h]
      rw [simplePos_of_not_lt h, blockMat, fromBlocks_apply₁₂, mul_apply_last hA C h] at h0
      exact h0

variable (r k) in
@[expose] def simpleKer (i : Fin r) : Subgroup (StatedSp r k) where
  carrier := {g | ∃ A C : Matrix (Fin r) (Fin r) k, IsUnitriangular A ∧ Cᵀ = C ∧
    ((g : GL (Fin r ⊕ Fin r) k) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) k) = blockMat A C ∧
    if h : i.val + 1 < r then A i ⟨i.val + 1, h⟩ = 0 else C i i = 0}
  one_mem' := simpleCond_iff.2 ⟨one_mem _, by
    rw [OneMemClass.coe_one, Units.val_one, one_apply_ne]
    intro h
    have := flagOrder_simplePos i
    rw [h] at this
    omega⟩
  mul_mem' {g h} hg hh := by
    obtain ⟨hg1, hg2⟩ := simpleCond_iff.1 hg
    obtain ⟨hh1, hh2⟩ := simpleCond_iff.1 hh
    exact simpleCond_iff.2 ⟨mul_mem hg1 hh1, by
      rw [mul_apply_of_adjacent hg1 hh1 (flagOrder_simplePos i), hg2, hh2, add_zero]⟩
  inv_mem' {g} hg := by
    obtain ⟨hg1, hg2⟩ := simpleCond_iff.1 hg
    exact simpleCond_iff.2 ⟨inv_mem hg1, by
      rw [inv_apply_of_adjacent hg1 (flagOrder_simplePos i), hg2, neg_zero]⟩

theorem mem_simpleKer_iff {g : StatedSp r k} {i : Fin r} :
    g ∈ simpleKer r k i ↔ g ∈ unipotent r k ∧ ((g : GL (Fin r ⊕ Fin r) k) :
      Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) k) (simplePos i).1 (simplePos i).2 = 0 :=
  simpleCond_iff

theorem simpleKer_le_unipotent (i : Fin r) : simpleKer r k i ≤ unipotent r k :=
  fun _ hg => (mem_simpleKer_iff.1 hg).1

end Simple

section SimpleMaps

variable {r : ℕ} {k : Type} [Field k]

variable (k) in
@[expose] noncomputable def etaS (i : Fin r) : SpecialLinearGroup (Fin 2) k →* StatedSp r k :=
  if h : i.val + 1 < r then rho i ⟨i.val + 1, h⟩ (succ_ne h) else lam i

theorem etaS_of_lt {i : Fin r} (h : i.val + 1 < r) :
    etaS k i = rho i ⟨i.val + 1, h⟩ (succ_ne h) :=
  dite_eq_left h

theorem etaS_of_not_lt {i : Fin r} (h : ¬i.val + 1 < r) : etaS k i = lam i :=
  dite_eq_right h

theorem vSL_add (a b : k) : vSL (a + b) = vSL a * vSL b := by
  refine Matrix.SpecialLinearGroup.ext _ _ fun x y => ?_
  rw [Matrix.SpecialLinearGroup.coe_mul, coe_vSL, coe_vSL, coe_vSL]
  fin_cases x <;> fin_cases y <;> simp [mul_apply, Fin.sum_univ_two, add_comm]

theorem vSL_zero : vSL (0 : k) = 1 := by
  refine Matrix.SpecialLinearGroup.ext _ _ fun x y => ?_
  rw [coe_vSL]
  fin_cases x <;> fin_cases y <;> simp

theorem uSL_inv (t : k) : (uSL t)⁻¹ = uSL (-t) :=
  inv_eq_of_mul_eq_one_right (by rw [← uSL_add, add_neg_cancel, uSL_zero])

theorem vSL_inv (t : k) : (vSL t)⁻¹ = vSL (-t) :=
  inv_eq_of_mul_eq_one_right (by rw [← vSL_add, add_neg_cancel, vSL_zero])

theorem transpose_upper (t : k) :
    (!![1, t; 0, 1] : Matrix (Fin 2) (Fin 2) k)ᵀ = !![1, 0; t, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem transpose_lower (t : k) :
    (!![1, 0; t, 1] : Matrix (Fin 2) (Fin 2) k)ᵀ = !![1, t; 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem fromBlocks_one_add_single (i j i' j' : Fin r) (c d : k) :
    fromBlocks (1 + single i j c) 0 0 (1 + single i' j' d) =
      (1 + single (Sum.inl i) (Sum.inl j) c + single (Sum.inr i') (Sum.inr j') d :
        Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) k) := by
  ext (x | x) (y | y) <;> simp [single_apply, one_apply]

theorem coe_etaS_uSL_of_lt {i : Fin r} (h : i.val + 1 < r) (t : k) :
    (((etaS k i (uSL t) : StatedSp r k) : GL (Fin r ⊕ Fin r) k) :
      Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) k) =
      1 + single (Sum.inl i) (Sum.inl ⟨i.val + 1, h⟩) t +
        single (Sum.inr ⟨i.val + 1, h⟩) (Sum.inr i) (-t) := by
  rw [etaS_of_lt h, coe_rho', uSL_inv, coe_uSL, coe_uSL, transpose_upper,
    pairMat_upper (succ_ne h), pairMat_lower (succ_ne h), fromBlocks_one_add_single]

theorem coe_etaS_vSL_of_lt {i : Fin r} (h : i.val + 1 < r) (t : k) :
    (((etaS k i (vSL t) : StatedSp r k) : GL (Fin r ⊕ Fin r) k) :
      Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) k) =
      1 + single (Sum.inl ⟨i.val + 1, h⟩) (Sum.inl i) t +
        single (Sum.inr i) (Sum.inr ⟨i.val + 1, h⟩) (-t) := by
  rw [etaS_of_lt h, coe_rho', vSL_inv, coe_vSL, coe_vSL, transpose_lower,
    pairMat_lower (succ_ne h), pairMat_upper (succ_ne h), fromBlocks_one_add_single]

theorem coe_etaS_uSL_of_not_lt {i : Fin r} (h : ¬i.val + 1 < r) (t : k) :
    (((etaS k i (uSL t) : StatedSp r k) : GL (Fin r ⊕ Fin r) k) :
      Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) k) = 1 + single (Sum.inl i) (Sum.inr i) t := by
  rw [etaS_of_not_lt h, coe_lam, coe_uSL, pairMat_upper Sum.inl_ne_inr]

theorem coe_etaS_vSL_of_not_lt {i : Fin r} (h : ¬i.val + 1 < r) (t : k) :
    (((etaS k i (vSL t) : StatedSp r k) : GL (Fin r ⊕ Fin r) k) :
      Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) k) = 1 + single (Sum.inr i) (Sum.inl i) t := by
  rw [etaS_of_not_lt h, coe_lam, coe_vSL, pairMat_lower Sum.inl_ne_inr]

theorem one_add_single_add_single_apply {a b a' b' : Fin r ⊕ Fin r} (hab : a ≠ b)
    (hab' : a' ≠ b') (c d : k) :
    (∀ x, (1 + single a b c + single a' b' d : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) k) x x =
      1) ∧
    ∀ x y, x ≠ y →
      (1 + single a b c + single a' b' d : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) k) x y ≠ 0 →
        (x = a ∧ y = b) ∨ (x = a' ∧ y = b') := by
  refine ⟨fun x => ?_, fun x y hxy h => ?_⟩
  · simp only [Matrix.add_apply, one_apply_eq, single_apply]
    rw [ite_eq_right (fun h' => hab (h'.1.trans h'.2.symm)),
      ite_eq_right (fun h' => hab' (h'.1.trans h'.2.symm))]
    simp
  · simp only [Matrix.add_apply, one_apply_ne hxy, single_apply, zero_add] at h
    by_cases h1 : a = x ∧ b = y
    · exact Or.inl ⟨h1.1.symm, h1.2.symm⟩
    by_cases h2 : a' = x ∧ b' = y
    · exact Or.inr ⟨h2.1.symm, h2.2.symm⟩
    rw [ite_eq_right h1, ite_eq_right h2, add_zero] at h
    exact absurd rfl h

theorem one_add_single_apply {a b : Fin r ⊕ Fin r} (hab : a ≠ b) (c : k) :
    (∀ x, (1 + single a b c : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) k) x x = 1) ∧
    ∀ x y, x ≠ y → (1 + single a b c : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) k) x y ≠ 0 →
      x = a ∧ y = b := by
  have h := one_add_single_add_single_apply hab hab c 0
  simp only [single_zero, add_zero] at h
  refine ⟨h.1, fun x y hxy hne => ?_⟩
  rcases h.2 x y hxy hne with h' | h' <;> exact h'

end SimpleMaps

section MatrixLevel

variable {r : ℕ} {k : Type} [Field k]

theorem inl_ne_inl_succ {i : Fin r} (h : i.val + 1 < r) :
    (Sum.inl i : Fin r ⊕ Fin r) ≠ Sum.inl ⟨i.val + 1, h⟩ :=
  Sum.inl_injective.ne (succ_ne h)

theorem inr_succ_ne_inr {i : Fin r} (h : i.val + 1 < r) :
    (Sum.inr ⟨i.val + 1, h⟩ : Fin r ⊕ Fin r) ≠ Sum.inr i :=
  Sum.inr_injective.ne (succ_ne h).symm

theorem inl_succ_ne_inl {i : Fin r} (h : i.val + 1 < r) :
    (Sum.inl ⟨i.val + 1, h⟩ : Fin r ⊕ Fin r) ≠ Sum.inl i :=
  Sum.inl_injective.ne (succ_ne h).symm

theorem inr_ne_inr_succ {i : Fin r} (h : i.val + 1 < r) :
    (Sum.inr i : Fin r ⊕ Fin r) ≠ Sum.inr ⟨i.val + 1, h⟩ :=
  Sum.inr_injective.ne (succ_ne h)

theorem etaS_uSL_mem_unipotent (i : Fin r) (t : k) : etaS k i (uSL t) ∈ unipotent r k := by
  rw [mem_unipotent_iff_flag]
  by_cases h : i.val + 1 < r
  · obtain ⟨hd, ho⟩ := one_add_single_add_single_apply (inl_ne_inl_succ h) (inr_succ_ne_inr h)
      t (-t)
    rw [coe_etaS_uSL_of_lt h]
    refine ⟨fun x y hxy => ?_, hd⟩
    by_contra hne
    have hxy' : x ≠ y := by
      rintro rfl
      exact lt_irrefl _ hxy
    rcases ho x y hxy' hne with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rw [flagOrder_inl, flagOrder_inl] at hxy
      simp at hxy
    · rw [flagOrder_inr, flagOrder_inr] at hxy
      simp only at hxy
      omega
  · obtain ⟨hd, ho⟩ := one_add_single_apply (Sum.inl_ne_inr : (Sum.inl i : Fin r ⊕ Fin r) ≠
      Sum.inr i) t
    rw [coe_etaS_uSL_of_not_lt h]
    refine ⟨fun x y hxy => ?_, hd⟩
    by_contra hne
    have hxy' : x ≠ y := by
      rintro rfl
      exact lt_irrefl _ hxy
    obtain ⟨rfl, rfl⟩ := ho x y hxy' hne
    rw [flagOrder_inl, flagOrder_inr] at hxy
    omega

theorem etaS_uSL_coord (i : Fin r) (t : k) :
    (((etaS k i (uSL t) : StatedSp r k) : GL (Fin r ⊕ Fin r) k) :
      Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) k) (simplePos i).1 (simplePos i).2 = t := by
  by_cases h : i.val + 1 < r
  · rw [simplePos_of_lt h, coe_etaS_uSL_of_lt h]
    simp [one_apply_ne (inl_ne_inl_succ h)]
  · rw [simplePos_of_not_lt h, coe_etaS_uSL_of_not_lt h]
    simp

theorem exists_etaS_uSL_mul_mem_simpleKer {g : StatedSp r k} (hg : g ∈ unipotent r k)
    (i : Fin r) :
    ∃ t : k, (etaS k i (uSL t))⁻¹ * g ∈ simpleKer r k i := by
  refine ⟨((g : GL (Fin r ⊕ Fin r) k) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) k)
    (simplePos i).1 (simplePos i).2, ?_⟩
  have hu := etaS_uSL_mem_unipotent (k := k) i (((g : GL (Fin r ⊕ Fin r) k) :
    Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) k) (simplePos i).1 (simplePos i).2)
  rw [mem_simpleKer_iff]
  refine ⟨mul_mem (inv_mem hu) hg, ?_⟩
  rw [mul_apply_of_adjacent (inv_mem hu) hg (flagOrder_simplePos i),
    inv_apply_of_adjacent hu (flagOrder_simplePos i), etaS_uSL_coord, neg_add_cancel]

theorem apply_inr_succ_inr {X : StatedSp r k} (hX : X ∈ unipotent r k) {i : Fin r}
    (h : i.val + 1 < r) :
    ((X : GL (Fin r ⊕ Fin r) k) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) k)
        (Sum.inr ⟨i.val + 1, h⟩) (Sum.inr i) =
      -((X : GL (Fin r ⊕ Fin r) k) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) k)
        (Sum.inl i) (Sum.inl ⟨i.val + 1, h⟩) := by
  obtain ⟨A, C, hA, -, hXA⟩ := hX
  rw [hXA, blockMat, fromBlocks_apply₂₂, fromBlocks_apply₁₁, transpose_apply]
  set j : Fin r := ⟨i.val + 1, h⟩
  have hij : i < j := Fin.lt_def.2 (by simp [j])
  have hinv := hA.inv
  have hmul : (A * A⁻¹) i j = 0 := by
    rw [mul_nonsing_inv A hA.isUnit_det, one_apply_ne (succ_ne h)]
  rw [mul_apply, Finset.sum_eq_add i j hij.ne] at hmul
  · rw [hA.2 i, one_mul, hinv.2 j, mul_one] at hmul
    linear_combination hmul
  · intro l _ hl
    rcases lt_or_gt_of_ne hl.1 with h1 | h1
    · rw [hA.1 h1, zero_mul]
    · have h2 : j < l := by
        have := Fin.lt_def.1 h1
        have hne : l.val ≠ j.val := fun e => hl.2 (Fin.ext e)
        exact Fin.lt_def.2 (by simp only [j] at hne ⊢; omega)
      rw [hinv.1 h2, mul_zero]
  · simp
  · simp

variable (r) in
@[expose] def simpleSwap (i : Fin r) : Equiv.Perm (Fin r ⊕ Fin r) :=
  if h : i.val + 1 < r then
    Equiv.sumCongr (Equiv.swap i ⟨i.val + 1, h⟩) (Equiv.swap i ⟨i.val + 1, h⟩)
  else Equiv.swap (Sum.inl i) (Sum.inr i)

theorem simpleSwap_of_lt {i : Fin r} (h : i.val + 1 < r) :
    simpleSwap r i = Equiv.sumCongr (Equiv.swap i ⟨i.val + 1, h⟩) (Equiv.swap i ⟨i.val + 1, h⟩) :=
  dite_eq_left h

theorem simpleSwap_of_not_lt {i : Fin r} (h : ¬i.val + 1 < r) :
    simpleSwap r i = Equiv.swap (Sum.inl i) (Sum.inr i) :=
  dite_eq_right h

theorem simpleSwap_inv (i : Fin r) : (simpleSwap r i)⁻¹ = simpleSwap r i := by
  by_cases h : i.val + 1 < r
  · rw [simpleSwap_of_lt h, Equiv.Perm.sumCongr_inv, Equiv.swap_inv]
  · rw [simpleSwap_of_not_lt h, Equiv.swap_inv]

theorem simpleSwap_simplePos (i : Fin r) :
    simpleSwap r i (simplePos i).1 = (simplePos i).2 ∧
      simpleSwap r i (simplePos i).2 = (simplePos i).1 := by
  by_cases h : i.val + 1 < r
  · rw [simpleSwap_of_lt h, simplePos_of_lt h]
    simp
  · rw [simpleSwap_of_not_lt h, simplePos_of_not_lt h]
    simp

theorem val_swap_succ {i : Fin r} (h : i.val + 1 < r) (a : Fin r) :
    ((Equiv.swap i ⟨i.val + 1, h⟩ a : Fin r) : ℕ) =
      if a.val = i.val then i.val + 1 else if a.val = i.val + 1 then i.val else a.val := by
  rw [Equiv.swap_apply_def]
  by_cases h1 : a = i
  · rw [ite_eq_left h1, ite_eq_left (congrArg Fin.val h1)]
  · rw [ite_eq_right h1, ite_eq_right (fun e => h1 (Fin.ext e))]
    by_cases h2 : a = ⟨i.val + 1, h⟩
    · rw [ite_eq_left h2, ite_eq_left (congrArg Fin.val h2)]
    · rw [ite_eq_right h2, ite_eq_right (fun e => h2 (Fin.ext e))]

theorem simpleSwap_flagOrder_lt {i : Fin r} {x y : Fin r ⊕ Fin r}
    (hxy : (flagOrder r x : ℕ) < flagOrder r y) (h1 : (x, y) ≠ simplePos i)
    (h2 : ∀ h : i.val + 1 < r, (x, y) ≠ (Sum.inr ⟨i.val + 1, h⟩, Sum.inr i)) :
    (flagOrder r (simpleSwap r i x) : ℕ) < flagOrder r (simpleSwap r i y) := by
  by_cases h : i.val + 1 < r
  · rw [simpleSwap_of_lt h]
    rw [simplePos_of_lt h] at h1
    have h2' := h2 h
    rcases x with a | a <;> rcases y with b | b <;>
      simp only [Equiv.sumCongr_apply, Sum.map_inl, Sum.map_inr, flagOrder_inl,
        flagOrder_inr] at hxy ⊢ <;>
      rw [val_swap_succ h, val_swap_succ h] <;>
      have ha := a.isLt <;> have hb := b.isLt
    · have hne : ¬(a.val = i.val ∧ b.val = i.val + 1) := by
        rintro ⟨e1, e2⟩
        exact h1 (by rw [show a = i from Fin.ext e1, show b = ⟨i.val + 1, h⟩ from Fin.ext e2])
      split_ifs <;> omega
    · split_ifs <;> omega
    · split_ifs <;> omega
    · have hne : ¬(a.val = i.val + 1 ∧ b.val = i.val) := by
        rintro ⟨e1, e2⟩
        exact h2' (by rw [show a = ⟨i.val + 1, h⟩ from Fin.ext e1, show b = i from Fin.ext e2])
      split_ifs <;> omega
  · rw [simpleSwap_of_not_lt h]
    rw [simplePos_of_not_lt h] at h1
    have hi := i.isLt
    have hfo : ∀ c : Fin r ⊕ Fin r, c ≠ Sum.inl i → c ≠ Sum.inr i →
        (flagOrder r c : ℕ) ≠ r - 1 ∧ (flagOrder r c : ℕ) ≠ r := by
      intro c hc1 hc2
      rcases c with c | c
      · rw [flagOrder_inl]
        have : c.val ≠ i.val := fun e => hc1 (by rw [Fin.ext e])
        have := c.isLt
        omega
      · rw [flagOrder_inr]
        have : c.val ≠ i.val := fun e => hc2 (by rw [Fin.ext e])
        have := c.isLt
        omega
    have hli : (flagOrder r (Sum.inl i) : ℕ) = r - 1 := by rw [flagOrder_inl]; omega
    have hri : (flagOrder r (Sum.inr i) : ℕ) = r := by rw [flagOrder_inr]; omega
    by_cases hx1 : x = Sum.inl i
    · subst hx1
      rw [Equiv.swap_apply_left, hri]
      by_cases hy2 : y = Sum.inr i
      · exact absurd (by rw [hy2]) h1
      have hy1 : y ≠ Sum.inl i := by rintro rfl; exact lt_irrefl _ hxy
      rw [Equiv.swap_apply_of_ne_of_ne hy1 hy2]
      have := hfo y hy1 hy2
      rw [hli] at hxy
      omega
    by_cases hx2 : x = Sum.inr i
    · subst hx2
      rw [Equiv.swap_apply_right, hli]
      rw [hri] at hxy
      by_cases hy1 : y = Sum.inl i
      · rw [hy1, hli] at hxy
        omega
      have hy2 : y ≠ Sum.inr i := fun e => by
        subst e
        rw [hri] at hxy
        omega
      rw [Equiv.swap_apply_of_ne_of_ne hy1 hy2]
      omega
    rw [Equiv.swap_apply_of_ne_of_ne hx1 hx2]
    have hfx := hfo x hx1 hx2
    by_cases hy1 : y = Sum.inl i
    · rw [hy1, Equiv.swap_apply_left, hri]
      rw [hy1, hli] at hxy
      omega
    by_cases hy2 : y = Sum.inr i
    · rw [hy2, Equiv.swap_apply_right, hli]
      rw [hy2, hri] at hxy
      omega
    rw [Equiv.swap_apply_of_ne_of_ne hy1 hy2]
    exact hxy

theorem conj_mem_simpleKer {g X : StatedSp r k} {i : Fin r}
    (hg : IsLinePerm (simpleSwap r i)
      ((g : GL (Fin r ⊕ Fin r) k) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) k))
    (hX : X ∈ simpleKer r k i) : g * X * g⁻¹ ∈ simpleKer r k i := by
  rw [mem_simpleKer_iff] at hX ⊢
  obtain ⟨hXU, hX0⟩ := hX
  obtain ⟨hlow, hdiag⟩ := mem_unipotent_iff_flag.1 hXU
  refine ⟨conj_mem_unipotent hg hdiag fun x y hxy hne => ?_, ?_⟩
  · have hlt : (flagOrder r x : ℕ) < flagOrder r y := by
      by_contra hle
      rcases Nat.lt_or_ge (flagOrder r y : ℕ) (flagOrder r x) with h' | h'
      · exact hne (hlow x y h')
      · exact hxy (flagOrder_injective_val (by omega))
    refine simpleSwap_flagOrder_lt hlt (fun e => hne ?_) (fun h e => hne ?_)
    · rw [show x = (simplePos i).1 from congrArg Prod.fst e,
        show y = (simplePos i).2 from congrArg Prod.snd e]
      exact hX0
    · rw [show x = Sum.inr ⟨i.val + 1, h⟩ from congrArg Prod.fst e,
        show y = Sum.inr i from congrArg Prod.snd e, apply_inr_succ_inr hXU h]
      rw [simplePos_of_lt h] at hX0
      rw [hX0, neg_zero]
  · obtain ⟨hs1, hs2⟩ := simpleSwap_simplePos (r := r) i
    have hc := conj_apply_of_isLinePerm hg
      ((X : GL (Fin r ⊕ Fin r) k) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) k)
      (simplePos i).2 (simplePos i).1
    rw [hs1, hs2] at hc
    change (((g : GL (Fin r ⊕ Fin r) k) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) k) *
      ((X : GL (Fin r ⊕ Fin r) k) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) k) *
      ((g⁻¹ : GL (Fin r ⊕ Fin r) k) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) k))
        (simplePos i).1 (simplePos i).2 = 0
    rw [hc, hlow _ _ (by rw [flagOrder_simplePos]; omega), mul_zero, zero_mul]

theorem conj_etaS_mem_unipotent_or {g : StatedSp r k} {σ : Equiv.Perm (Fin r ⊕ Fin r)}
    (hσ : σ ∈ signedPermGroup r)
    (hg : IsLinePerm σ ((g : GL (Fin r ⊕ Fin r) k) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) k))
    (i : Fin r) :
    (∀ t : k, g * etaS k i (uSL t) * g⁻¹ ∈ unipotent r k) ∨
      ∀ t : k, g * etaS k i (vSL t) * g⁻¹ ∈ unipotent r k := by
  have hsw : ∀ c, (flagOrder r (σ c.swap) : ℕ) = 2 * r - 1 - flagOrder r (σ c) := fun c => by
    rw [hσ c, flagOrder_swap]
  have hne : (flagOrder r (σ (simplePos i).1) : ℕ) ≠ flagOrder r (σ (simplePos i).2) := by
    intro e
    have := σ.injective (flagOrder_injective_val e)
    have hfo := flagOrder_simplePos i
    rw [this] at hfo
    omega
  have hlt1 := flagOrder_lt (σ (simplePos i).1)
  have hlt2 := flagOrder_lt (σ (simplePos i).2)
  rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
  · left
    intro t
    by_cases h : i.val + 1 < r
    · obtain ⟨hd, ho⟩ := one_add_single_add_single_apply (inl_ne_inl_succ h) (inr_succ_ne_inr h)
        t (-t)
      rw [simplePos_of_lt h] at hlt hlt1 hlt2
      dsimp only at hlt hlt1 hlt2
      refine conj_mem_unipotent hg (by rw [coe_etaS_uSL_of_lt h]; exact hd) fun x y hxy hX => ?_
      rw [coe_etaS_uSL_of_lt h] at hX
      rcases ho x y hxy hX with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hlt
      · have e1 := hsw (Sum.inl ⟨i.val + 1, h⟩)
        have e2 := hsw (Sum.inl i)
        simp only [Sum.swap_inl] at e1 e2
        omega
    · obtain ⟨hd, ho⟩ := one_add_single_apply (Sum.inl_ne_inr : (Sum.inl i : Fin r ⊕ Fin r) ≠
        Sum.inr i) t
      rw [simplePos_of_not_lt h] at hlt
      dsimp only at hlt
      refine conj_mem_unipotent hg (by rw [coe_etaS_uSL_of_not_lt h]; exact hd)
        fun x y hxy hX => ?_
      rw [coe_etaS_uSL_of_not_lt h] at hX
      obtain ⟨rfl, rfl⟩ := ho x y hxy hX
      exact hlt
  · right
    intro t
    by_cases h : i.val + 1 < r
    · obtain ⟨hd, ho⟩ := one_add_single_add_single_apply (inl_succ_ne_inl h) (inr_ne_inr_succ h)
        t (-t)
      rw [simplePos_of_lt h] at hgt hlt1 hlt2
      dsimp only at hgt hlt1 hlt2
      refine conj_mem_unipotent hg (by rw [coe_etaS_vSL_of_lt h]; exact hd) fun x y hxy hX => ?_
      rw [coe_etaS_vSL_of_lt h] at hX
      rcases ho x y hxy hX with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hgt
      · have e1 := hsw (Sum.inl ⟨i.val + 1, h⟩)
        have e2 := hsw (Sum.inl i)
        simp only [Sum.swap_inl] at e1 e2
        omega
    · obtain ⟨hd, ho⟩ := one_add_single_apply (Sum.inr_ne_inl : (Sum.inr i : Fin r ⊕ Fin r) ≠
        Sum.inl i) t
      rw [simplePos_of_not_lt h] at hgt
      dsimp only at hgt
      refine conj_mem_unipotent hg (by rw [coe_etaS_vSL_of_not_lt h]; exact hd)
        fun x y hxy hX => ?_
      rw [coe_etaS_vSL_of_not_lt h] at hX
      obtain ⟨rfl, rfl⟩ := ho x y hxy hX
      exact hgt

theorem borelSubgroup_eq_sup : borelSubgroup r k = unipotent r k ⊔ torus r k := by
  refine le_antisymm (fun g hg => ?_) (sup_le
    unipotent_le_borelSubgroup
    torus_le_borelSubgroup)
  set d := diagHom r k ⟨g, hg⟩
  have ht : torusHom d ∈ borelSubgroup r k :=
    torus_le_borelSubgroup ⟨d, rfl⟩
  have hdt : diagHom r k ⟨_, ht⟩ = d := by
    funext i
    apply Units.ext
    rw [coe_diagHom_apply, coe_torusHom]
    simp
  have hker : (⟨g, hg⟩ * (⟨_, ht⟩ : borelSubgroup r k)⁻¹ : borelSubgroup r k) ∈
      (diagHom r k).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hdt, mul_inv_cancel]
  rw [ker_diagHom,
    Subgroup.mem_subgroupOf] at hker
  have hg' : g = (g * (torusHom d)⁻¹) * torusHom d := by rw [inv_mul_cancel_right]
  rw [hg']
  exact mul_mem (Subgroup.mem_sup_left hker) (Subgroup.mem_sup_right ⟨d, rfl⟩)

theorem unipotent_inf_torus : unipotent r k ⊓ torus r k = ⊥ := by
  rw [eq_bot_iff]
  rintro _ ⟨hU, d, rfl⟩
  have hd := (mem_unipotent_iff_flag.1 hU).2
  have h1 : d = 1 := by
    funext i
    apply Units.ext
    have := hd (Sum.inl i)
    rw [coe_torusHom] at this
    simpa using this
  rw [h1, map_one]
  exact one_mem _

theorem conj_mem_unipotent_of_mem_borel {b u : StatedSp r k} (hb : b ∈ borelSubgroup r k)
    (hu : u ∈ unipotent r k) : b * u * b⁻¹ ∈ unipotent r k := by
  have hN :=
    unipotent_subgroupOf_borelSubgroup_normal
      (r := r) (K := k)
  have hu' : (⟨u,
      unipotent_le_borelSubgroup hu⟩ :
      borelSubgroup r k) ∈ (unipotent r k).subgroupOf (borelSubgroup r k) := hu
  exact hN.conj_mem _ hu' ⟨b, hb⟩

end MatrixLevel

section LiftDefs

variable {r : ℕ} {k : Type} [Field k] {E : Type*} [Group E] (π : E →* StatedSp r k)

@[expose] noncomputable def etaSLift (i : Fin r) : SpecialLinearGroup (Fin 2) k →* E :=
  sl2Lift π (etaS k i)

@[expose] noncomputable def xPlus (i : Fin r) (t : k) : E := etaSLift π i (uSL t)

@[expose] noncomputable def xMinus (i : Fin r) (t : k) : E := etaSLift π i (vSL t)

@[expose] noncomputable def dLift (i : Fin r) (a : kˣ) : E := etaSLift π i (sl2Diag a)

theorem sLift_eq_etaSLift (i : Fin r) : sLift π i = etaSLift π i sl2W := by
  by_cases h : i.val + 1 < r
  · rw [sLift_of_lt h, vLiftRho, rhoLift, etaSLift, etaS_of_lt h]
  · rw [sLift_of_not_lt h, vLift, lamLift, etaSLift, etaS_of_not_lt h]

theorem xPlus_mul_sLift (i : Fin r) {t : k} (ht : t ≠ 0) :
    xPlus π i t * sLift π i = xMinus π i t⁻¹ * dLift π i (Units.mk0 t ht) * xPlus π i (-t⁻¹) := by
  have h2 : uSL t * (sl2W : SpecialLinearGroup (Fin 2) k) =
      vSL t⁻¹ * sl2Diag (Units.mk0 t ht) * uSL (-t⁻¹) := by
    refine Matrix.SpecialLinearGroup.ext _ _ fun x y => ?_
    simp only [Matrix.SpecialLinearGroup.coe_mul, coe_uSL, coe_vSL, coe_sl2W, coe_sl2Diag,
      Units.val_mk0, Units.val_inv_eq_inv_val]
    fin_cases x <;> fin_cases y <;> simp [mul_apply, Fin.sum_univ_two, ht]
  rw [sLift_eq_etaSLift, xPlus, xMinus, dLift, xPlus, ← map_mul, h2, map_mul, map_mul]

end LiftDefs

section Lifts

variable {r : ℕ} {k : Type} [Field k] [Finite k] {E : Type*} [Group E] [Finite E]
  {π : E →* StatedSp r k}

omit [Finite k] [Finite E] in
theorem uSL_pow (t : k) (n : ℕ) : uSL t ^ n = uSL ((n : k) * t) := by
  induction n with
  | zero => rw [pow_zero, Nat.cast_zero, zero_mul, uSL_zero]
  | succ n ih => rw [pow_succ, ih, ← uSL_add, Nat.cast_succ, add_mul, one_mul]

omit [Finite k] [Finite E] in
theorem vSL_pow (t : k) (n : ℕ) : vSL t ^ n = vSL ((n : k) * t) := by
  induction n with
  | zero => rw [pow_zero, Nat.cast_zero, zero_mul, vSL_zero]
  | succ n ih => rw [pow_succ, ih, ← vSL_add, Nat.cast_succ, add_mul, one_mul]

omit [Finite k] [Finite E] in
theorem exists_orderOf_etaSLift_uSL [Fact (ringChar k).Prime] (i : Fin r) (t : k) :
    ∃ n : ℕ, orderOf (etaSLift π i (uSL t)) = ringChar k ^ n := by
  refine exists_orderOf_eq_pow_of_pow_eq_one (n := 1) ?_
  rw [pow_one, ← map_pow, uSL_pow, CharP.cast_eq_zero, zero_mul, uSL_zero, map_one]

omit [Finite k] [Finite E] in
theorem exists_orderOf_etaSLift_vSL [Fact (ringChar k).Prime] (i : Fin r) (t : k) :
    ∃ n : ℕ, orderOf (etaSLift π i (vSL t)) = ringChar k ^ n := by
  refine exists_orderOf_eq_pow_of_pow_eq_one (n := 1) ?_
  rw [pow_one, ← map_pow, vSL_pow, CharP.cast_eq_zero, zero_mul, vSL_zero, map_one]

omit [Finite E] in
theorem isPGroup_unipotent : IsPGroup (ringChar k) (unipotent r k) := by
  have := Fintype.ofFinite k
  obtain ⟨n, hp, hcard⟩ := FiniteField.card k (ringChar k)
  have : Fact (ringChar k).Prime := ⟨hp⟩
  refine IsPGroup.of_card (n := n * r ^ 2) ?_
  rw [card_unipotent, Nat.card_eq_fintype_card,
    hcard, ← pow_mul]

omit [Finite E] in
theorem isPGroup_simpleKer (i : Fin r) : IsPGroup (ringChar k) (simpleKer r k i) :=
  isPGroup_unipotent.to_le (simpleKer_le_unipotent i)

variable [Fact (ringChar k).Prime] (hcen : π.ker ≤ Subgroup.center E)
include hcen

omit [Finite k] in
theorem mem_liftSubgroup_of {V : Subgroup (StatedSp r k)} (hV : IsPGroup (ringChar k) V) {x : E}
    (hx : π x ∈ V) (hxo : ∃ n : ℕ, orderOf x = ringChar k ^ n) :
    x ∈ liftSubgroup (ringChar k) π V :=
  (mem_liftSubgroup_iff hcen hV).2 ⟨hx, hxo⟩

omit [Finite k] in
theorem liftSubgroup_mono {V W : Subgroup (StatedSp r k)} (hW : IsPGroup (ringChar k) W)
    (hVW : V ≤ W) : liftSubgroup (ringChar k) π V ≤ liftSubgroup (ringChar k) π W := by
  intro x hx
  obtain ⟨hx1, hx2⟩ := (mem_liftSubgroup_iff hcen (hW.to_le hVW)).1 hx
  exact mem_liftSubgroup_of hcen hW (hVW hx1) hx2

omit [Finite k] in
theorem conj_mem_liftSubgroup {V W : Subgroup (StatedSp r k)} (hV : IsPGroup (ringChar k) V)
    (hW : IsPGroup (ringChar k) W) {e : E} (he : ∀ u ∈ V, π e * u * (π e)⁻¹ ∈ W) {x : E}
    (hx : x ∈ liftSubgroup (ringChar k) π V) : e * x * e⁻¹ ∈ liftSubgroup (ringChar k) π W := by
  obtain ⟨hx1, n, hn⟩ := (mem_liftSubgroup_iff hcen hV).1 hx
  refine mem_liftSubgroup_of hcen hW ?_ ⟨n, ?_⟩
  · rw [map_mul, map_mul, map_inv]
    exact he _ hx1
  · rw [← hn]
    exact MulEquiv.orderOf_eq (MulAut.conj e) x

end Lifts

section Factorization

variable {r : ℕ} {k : Type} [Field k] [Finite k] {E : Type*} [Group E] [Finite E]
  {π : E →* StatedSp r k} [Fact (ringChar k).Prime] (hS : LargeHyp π)
include hS

omit [Fact (ringChar k).Prime] in
theorem pi_etaSLift (i : Fin r) (g : SpecialLinearGroup (Fin 2) k) :
    π (etaSLift π i g) = etaS k i g :=
  hS.map_lift _ g

theorem xPlus_mem_liftUnipotent (i : Fin r) (t : k) :
    xPlus π i t ∈ liftSubgroup (ringChar k) π (unipotent r k) :=
  mem_liftSubgroup_of hS.ext.cen isPGroup_unipotent
    (by rw [xPlus, pi_etaSLift hS]; exact etaS_uSL_mem_unipotent i t)
    (exists_orderOf_etaSLift_uSL i t)

omit [Fact (ringChar k).Prime] in
theorem pi_mem_torus {e : E} (he : e ∈ liftTorus π) : π e ∈ torus r k := by
  obtain ⟨t, rfl⟩ := (range_thetaHom hS).ge he
  exact ⟨t, by rw [← MonoidHom.comp_apply π, comp_thetaHom hS]⟩

theorem liftTorus_le_normalizer :
    liftTorus π ≤ Subgroup.normalizer
      (liftSubgroup (ringChar k) π (unipotent r k) : Set E) := by
  have key : ∀ e ∈ liftTorus π, ∀ x ∈ liftSubgroup (ringChar k) π (unipotent r k),
      e * x * e⁻¹ ∈ liftSubgroup (ringChar k) π (unipotent r k) := fun e he x hx =>
    conj_mem_liftSubgroup hS.ext.cen isPGroup_unipotent isPGroup_unipotent
      (fun u hu => conj_mem_unipotent_of_mem_borel
        (torus_le_borelSubgroup
          (pi_mem_torus hS he)) hu) hx
  intro h hh
  rw [Subgroup.mem_set_normalizer_iff]
  intro x
  refine ⟨key h hh x, fun hx => ?_⟩
  have := key h⁻¹ (inv_mem hh) _ hx
  simpa [mul_assoc] using this

theorem mem_liftBorel_iff {x : E} :
    x ∈ liftSubgroup (ringChar k) π (unipotent r k) ⊔ liftTorus π ↔
      ∃ u ∈ liftSubgroup (ringChar k) π (unipotent r k), ∃ h ∈ liftTorus π, x = u * h := by
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left _ _
    (liftTorus_le_normalizer hS), Set.mem_mul]
  exact ⟨fun ⟨u, hu, h, hh, e⟩ => ⟨u, hu, h, hh, e.symm⟩,
    fun ⟨u, hu, h, hh, e⟩ => ⟨u, hu, h, hh, e.symm⟩⟩

variable (hC : ¬ringChar k ∣ Nat.card π.ker)
include hC

theorem map_liftBorel :
    (liftSubgroup (ringChar k) π (unipotent r k) ⊔ liftTorus π).map π = borelSubgroup r k := by
  rw [Subgroup.map_sup, borelSubgroup_eq_sup]
  congr 1
  · refine le_antisymm (Subgroup.map_le_iff_le_comap.2
      (liftSubgroup_le_comap hS.ext.cen isPGroup_unipotent)) fun u hu => ?_
    exact ⟨_, pLift_mem_liftSubgroup hS.ext.surj hS.ext.cen hC isPGroup_unipotent hu,
      map_pLift hS.ext.surj hC (exists_orderOf_eq_pow_of_mem isPGroup_unipotent ⟨u, hu⟩)⟩
  · refine le_antisymm (Subgroup.map_le_iff_le_comap.2 fun e he => pi_mem_torus hS he) ?_
    rintro _ ⟨t, rfl⟩
    exact ⟨thetaHom hS t, (range_thetaHom hS).le ⟨t, rfl⟩, by
      rw [← MonoidHom.comp_apply π, comp_thetaHom hS]⟩

theorem injective_pi_liftBorel :
    Function.Injective
      (π.comp (liftSubgroup (ringChar k) π (unipotent r k) ⊔ liftTorus π).subtype) := by
  rw [injective_iff_map_eq_one]
  rintro ⟨x, hx⟩ h1
  have h1' : π x = 1 := h1
  obtain ⟨u, hu, h, hh, rfl⟩ := (mem_liftBorel_iff hS).1 hx
  have huh : π u = (π h)⁻¹ := eq_inv_of_mul_eq_one_left (by rw [← map_mul]; exact h1')
  have hmem : π u ∈ unipotent r k ⊓ torus r k :=
    Subgroup.mem_inf.2 ⟨liftSubgroup_le_comap hS.ext.cen isPGroup_unipotent hu, by
      rw [huh]
      exact inv_mem (pi_mem_torus hS hh)⟩
  rw [unipotent_inf_torus, Subgroup.mem_bot] at hmem
  obtain ⟨-, n, hn⟩ := (mem_liftSubgroup_iff hS.ext.cen isPGroup_unipotent).1 hu
  have hu1 : u = 1 := eq_one_of_mem_ker hC hmem (n := n) (by rw [← hn, pow_orderOf_eq_one])
  have hh1 : π h = 1 := by rw [hmem, eq_comm, inv_eq_one] at huh; exact huh
  have hh2 : h = 1 := by
    have := injective_pi_comp hS (a₁ := ⟨h, liftTorus_le_liftWeyl hh⟩) (a₂ := 1)
      (by rw [map_one]; exact hh1)
    exact congrArg Subtype.val this
  apply Subtype.ext
  simp [hu1, hh2]

omit hC in
theorem mem_liftBorel_iff_xPlus (i : Fin r) {x : E} :
    x ∈ liftSubgroup (ringChar k) π (unipotent r k) ⊔ liftTorus π ↔
      ∃ t : k, ∃ u ∈ liftSubgroup (ringChar k) π (simpleKer r k i), ∃ h ∈ liftTorus π,
        x = xPlus π i t * u * h := by
  constructor
  · intro hx
    obtain ⟨u, hu, h, hh, rfl⟩ := (mem_liftBorel_iff hS).1 hx
    obtain ⟨t, ht⟩ := exists_etaS_uSL_mul_mem_simpleKer
      (liftSubgroup_le_comap hS.ext.cen isPGroup_unipotent hu) i
    refine ⟨t, (xPlus π i t)⁻¹ * u, ?_, h, hh, by group⟩
    have hmem : (xPlus π i t)⁻¹ * u ∈ liftSubgroup (ringChar k) π (unipotent r k) :=
      mul_mem (inv_mem (xPlus_mem_liftUnipotent hS i t)) hu
    obtain ⟨-, hn⟩ := (mem_liftSubgroup_iff hS.ext.cen isPGroup_unipotent).1 hmem
    refine mem_liftSubgroup_of hS.ext.cen (isPGroup_simpleKer i) ?_ hn
    rw [map_mul, map_inv, xPlus, pi_etaSLift hS]
    exact ht
  · rintro ⟨t, u, hu, h, hh, rfl⟩
    refine mul_mem (mul_mem (Subgroup.mem_sup_left (xPlus_mem_liftUnipotent hS i t))
      (Subgroup.mem_sup_left ?_)) (Subgroup.mem_sup_right hh)
    exact liftSubgroup_mono hS.ext.cen isPGroup_unipotent (simpleKer_le_unipotent i) hu

omit hC [Fact (ringChar k).Prime] in
theorem isLinePerm_pi_sLift (i : Fin r) :
    IsLinePerm (simpleSwap r i) (((π (sLift π i) : StatedSp r k) : GL (Fin r ⊕ Fin r) k) :
      Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) k) := by
  by_cases h : i.val + 1 < r
  · rw [simpleSwap_of_lt h, sLift_of_lt h, pi_vLiftRho hS]
    exact isLinePerm_rho_sl2W _
  · rw [simpleSwap_of_not_lt h, sLift_of_not_lt h, pi_vLift hS]
    exact isLinePerm_lam_sl2W _

omit hC in
theorem sLift_mem_normalizer_liftSimpleKer (i : Fin r) :
    sLift π i ∈ Subgroup.normalizer
      (liftSubgroup (ringChar k) π (simpleKer r k i) : Set E) := by
  have hg := isLinePerm_pi_sLift hS i
  have hg' : IsLinePerm (simpleSwap r i)
      (((π (sLift π i)⁻¹ : StatedSp r k) : GL (Fin r ⊕ Fin r) k) :
        Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) k) := by
    rw [map_inv, Subgroup.coe_inv, ← simpleSwap_inv]
    exact hg.inv
  have key : ∀ e : E, IsLinePerm (simpleSwap r i)
      (((π e : StatedSp r k) : GL (Fin r ⊕ Fin r) k) :
        Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) k) →
      ∀ x ∈ liftSubgroup (ringChar k) π (simpleKer r k i),
        e * x * e⁻¹ ∈ liftSubgroup (ringChar k) π (simpleKer r k i) := fun e he x hx =>
    conj_mem_liftSubgroup hS.ext.cen (isPGroup_simpleKer i) (isPGroup_simpleKer i)
      (fun u hu => conj_mem_simpleKer he hu) hx
  rw [Subgroup.mem_set_normalizer_iff]
  intro x
  refine ⟨key _ hg x, fun hx => ?_⟩
  have := key _ hg' _ hx
  simpa [mul_assoc] using this

omit hC [Fact (ringChar k).Prime] in
theorem dLift_mem (i : Fin r) (a : kˣ) : dLift π i a ∈ liftTorus π := by
  by_cases h : i.val + 1 < r
  · have e : dLift π i a = hLiftRho π i ⟨i.val + 1, h⟩ (succ_ne h) a := by
      rw [dLift, etaSLift, etaS_of_lt h]
      rfl
    rw [e]
    exact hLiftRho_mem hS _ a
  · have e : dLift π i a = hLift π i a := by
      rw [dLift, etaSLift, etaS_of_not_lt h]
      rfl
    rw [e]
    exact hLift_mem i a

omit hC in
theorem conj_xPlus_or_xMinus_mem {v : E} (hv : v ∈ liftWeyl π) (i : Fin r) :
    (∀ t : k, v * xPlus π i t * v⁻¹ ∈ liftSubgroup (ringChar k) π (unipotent r k)) ∨
      ∀ t : k, v * xMinus π i t * v⁻¹ ∈ liftSubgroup (ringChar k) π (unipotent r k) := by
  have hσ := (weylHom hS ⟨v, hv⟩).2
  have hg := isLinePerm_weylHom hS ⟨v, hv⟩
  have horder : ∀ x : E, (∃ n : ℕ, orderOf x = ringChar k ^ n) →
      ∃ n : ℕ, orderOf (v * x * v⁻¹) = ringChar k ^ n := fun x ⟨n, hn⟩ =>
    ⟨n, by rw [← hn]; exact MulEquiv.orderOf_eq (MulAut.conj v) x⟩
  rcases conj_etaS_mem_unipotent_or hσ hg i with h | h
  · left
    intro t
    refine mem_liftSubgroup_of hS.ext.cen isPGroup_unipotent ?_
      (horder _ (exists_orderOf_etaSLift_uSL i t))
    rw [map_mul, map_mul, map_inv, xPlus, pi_etaSLift hS]
    exact h t
  · right
    intro t
    refine mem_liftSubgroup_of hS.ext.cen isPGroup_unipotent ?_
      (horder _ (exists_orderOf_etaSLift_vSL i t))
    rw [map_mul, map_mul, map_inv, xMinus, pi_etaSLift hS]
    exact h t

end Factorization

theorem odd_symplectic_cross_characteristic_central_prime_triangular_factorization
    {k : Type} [Field k] [Finite k] (hk : ringChar k ≠ 2) {r : ℕ} (_hr : 1 ≤ r) {E : Type*}
    [Group E] [Finite E] {π : E →* StatedSp r k} {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hpℓ : p ≠ ringChar k) (hπ : Function.Surjective π) (hcen : π.ker ≤ Subgroup.center E)
    (hpk : IsPGroup p π.ker) :
    (∀ P : Sylow (ringChar k) ((unipotent r k).comap π),
      (P : Subgroup ((unipotent r k).comap π)).map ((unipotent r k).comap π).subtype =
        liftSubgroup (ringChar k) π (unipotent r k)) ∧
    liftTorus π ≤ Subgroup.normalizer (liftSubgroup (ringChar k) π (unipotent r k) : Set E) ∧
    (∀ x : E, x ∈ liftSubgroup (ringChar k) π (unipotent r k) ⊔ liftTorus π ↔
      ∃ u ∈ liftSubgroup (ringChar k) π (unipotent r k), ∃ h ∈ liftTorus π, x = u * h) ∧
    (liftSubgroup (ringChar k) π (unipotent r k) ⊔ liftTorus π).map π = borelSubgroup r k ∧
    Function.Injective
      (π.comp (liftSubgroup (ringChar k) π (unipotent r k) ⊔ liftTorus π).subtype) ∧
    ∀ i : Fin r,
      π.comp (etaSLift π i) = etaS k i ∧
      (∀ h : i.val + 1 < r, etaSLift π i = rhoLift π i ⟨i.val + 1, h⟩ (succ_ne h)) ∧
      (¬i.val + 1 < r → etaSLift π i = lamLift π i) ∧
      sLift π i = etaSLift π i sl2W ∧
      (∀ x : E, x ∈ liftSubgroup (ringChar k) π (unipotent r k) ⊔ liftTorus π ↔
        ∃ t : k, ∃ u ∈ liftSubgroup (ringChar k) π (simpleKer r k i), ∃ h ∈ liftTorus π,
          x = xPlus π i t * u * h) ∧
      sLift π i ∈ Subgroup.normalizer
        (liftSubgroup (ringChar k) π (simpleKer r k i) : Set E) ∧
      sLift π i ∈ Subgroup.normalizer (liftTorus π : Set E) ∧
      (∀ (t : k) (ht : t ≠ 0), xPlus π i t * sLift π i =
        xMinus π i t⁻¹ * dLift π i (Units.mk0 t ht) * xPlus π i (-t⁻¹)) ∧
      (∀ a : kˣ, dLift π i a ∈ liftTorus π) ∧
      ∀ v ∈ liftWeyl π,
        (∀ t : k, v * xPlus π i t * v⁻¹ ∈ liftSubgroup (ringChar k) π (unipotent r k)) ∨
        ∀ t : k, v * xMinus π i t * v⁻¹ ∈ liftSubgroup (ringChar k) π (unipotent r k) := by
  have := Fintype.ofFinite k
  obtain ⟨n, hℓ, -⟩ := FiniteField.card k (ringChar k)
  have : Fact (ringChar k).Prime := ⟨hℓ⟩
  have hS : LargeHyp π := ⟨hk, ⟨hπ, hcen, ⟨p, hp, hp3, hpk⟩⟩⟩
  have hC : ¬ringChar k ∣ Nat.card π.ker := by
    obtain ⟨m, hm⟩ := hpk.exists_card_dvd_pow
    intro hdvd
    exact hpℓ ((Nat.prime_dvd_prime_iff_eq hℓ hp).1 (hℓ.dvd_of_dvd_pow (hdvd.trans hm))).symm
  refine ⟨sylow_map_eq_liftSubgroup hcen isPGroup_unipotent, liftTorus_le_normalizer hS,
    fun x => mem_liftBorel_iff hS, map_liftBorel hS hC, injective_pi_liftBorel hS hC,
    fun i => ⟨comp_sl2Lift_large hk hS.ext _, fun h => ?_, fun h => ?_, sLift_eq_etaSLift π i,
      fun x => mem_liftBorel_iff_xPlus hS i, sLift_mem_normalizer_liftSimpleKer hS i,
      liftWeyl_le_normalizer hS (sLift_mem i), fun t ht => xPlus_mul_sLift π i ht, dLift_mem hS i,
      fun v hv => conj_xPlus_or_xMinus_mem hS hv i⟩⟩
  · rw [etaSLift, etaS_of_lt h]
    rfl
  · rw [etaSLift, etaS_of_not_lt h]
    rfl

end CFSG.RankThree.CentralLiftSO.Sp
