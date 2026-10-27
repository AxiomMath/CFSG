module

public import CFSG.RankThree.Chevalley.SteinbergBNF4A2RootTraces
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedTools

public noncomputable section

namespace CFSG.RankThree.Chevalley

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley Matrix SteinbergBN
  Matrix.SpecialLinearGroup
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag (blockSL)
open scoped MatrixGroups

section Transvection

variable {L : Type} [Field L]

theorem exists_transvection_eq_of_simple (φ : SL(3, L) →* SL(3, L)) {μ₁ μ₂ μ₃ μ₄ : Lˣ}
    (h₁ : ∀ c, φ (t01 c) = t01 (μ₁ * c)) (h₂ : ∀ c, φ (t10 c) = t10 (μ₂ * c))
    (h₃ : ∀ c, φ (t12 c) = t12 (μ₃ * c)) (h₄ : ∀ c, φ (t21 c) = t21 (μ₄ * c)) :
    ∀ (a b : Fin 3) (hab : a ≠ b), ∃ β : Lˣ, ∀ c,
      φ (transvection hab c) = transvection hab ((β : L) * c) := by
  have h02 : ∀ c, φ (transvection (show (0 : Fin 3) ≠ 2 by decide) c) =
      transvection (show (0 : Fin 3) ≠ 2 by decide) (((μ₁ * μ₃ : Lˣ) : L) * c) := fun c => by
    have e := commutatorElement_transvection (show (0 : Fin 3) ≠ 1 by decide)
      (show (1 : Fin 3) ≠ 2 by decide) (show (0 : Fin 3) ≠ 2 by decide) (1 : L) c
    rw [one_mul] at e
    rw [← e, map_commutatorElement, h₁, h₃, commutatorElement_transvection
      (show (0 : Fin 3) ≠ 1 by decide) (show (1 : Fin 3) ≠ 2 by decide)
      (show (0 : Fin 3) ≠ 2 by decide), Units.val_mul]
    congr 1
    ring
  have h20 : ∀ c, φ (transvection (show (2 : Fin 3) ≠ 0 by decide) c) =
      transvection (show (2 : Fin 3) ≠ 0 by decide) (((μ₄ * μ₂ : Lˣ) : L) * c) := fun c => by
    have e := commutatorElement_transvection (show (2 : Fin 3) ≠ 1 by decide)
      (show (1 : Fin 3) ≠ 0 by decide) (show (2 : Fin 3) ≠ 0 by decide) c (1 : L)
    rw [mul_one] at e
    rw [← e, map_commutatorElement, h₄, h₂, commutatorElement_transvection
      (show (2 : Fin 3) ≠ 1 by decide) (show (1 : Fin 3) ≠ 0 by decide)
      (show (2 : Fin 3) ≠ 0 by decide), Units.val_mul]
    congr 1
    ring
  intro a b hab
  fin_cases a <;> fin_cases b
  · exact absurd rfl hab
  · exact ⟨μ₁, h₁⟩
  · exact ⟨μ₁ * μ₃, h02⟩
  · exact ⟨μ₂, h₂⟩
  · exact absurd rfl hab
  · exact ⟨μ₃, h₃⟩
  · exact ⟨μ₄ * μ₂, h20⟩
  · exact ⟨μ₄, h₄⟩
  · exact absurd rfl hab

theorem exists_transvection_swap_eq_of_simple (φ : SL(3, L) →* SL(3, L)) {μ₁ μ₂ μ₃ μ₄ : Lˣ}
    (h₁ : ∀ c, φ (t01 c) = t10 (μ₁ * c)) (h₂ : ∀ c, φ (t10 c) = t01 (μ₂ * c))
    (h₃ : ∀ c, φ (t12 c) = t21 (μ₃ * c)) (h₄ : ∀ c, φ (t21 c) = t12 (μ₄ * c)) :
    ∀ (a b : Fin 3) (hab : a ≠ b), ∃ β : Lˣ, ∀ c,
      φ (transvection hab c) = transvection hab.symm ((β : L) * c) := by
  have h02 : ∀ c, φ (transvection (show (0 : Fin 3) ≠ 2 by decide) c) =
      transvection (show (2 : Fin 3) ≠ 0 by decide) (((-(μ₁ * μ₃) : Lˣ) : L) * c) := fun c => by
    have e := commutatorElement_transvection (show (0 : Fin 3) ≠ 1 by decide)
      (show (1 : Fin 3) ≠ 2 by decide) (show (0 : Fin 3) ≠ 2 by decide) (1 : L) c
    rw [one_mul] at e
    rw [← e, map_commutatorElement, h₁, h₃, ← commutatorElement_inv,
      commutatorElement_transvection (show (2 : Fin 3) ≠ 1 by decide)
        (show (1 : Fin 3) ≠ 0 by decide) (show (2 : Fin 3) ≠ 0 by decide),
      SpecialLinearGroup.transvection_inv]
    congr 1
    simp only [Units.val_neg, Units.val_mul]
    ring
  have h20 : ∀ c, φ (transvection (show (2 : Fin 3) ≠ 0 by decide) c) =
      transvection (show (0 : Fin 3) ≠ 2 by decide) (((-(μ₄ * μ₂) : Lˣ) : L) * c) := fun c => by
    have e := commutatorElement_transvection (show (2 : Fin 3) ≠ 1 by decide)
      (show (1 : Fin 3) ≠ 0 by decide) (show (2 : Fin 3) ≠ 0 by decide) c (1 : L)
    rw [mul_one] at e
    rw [← e, map_commutatorElement, h₄, h₂, ← commutatorElement_inv,
      commutatorElement_transvection (show (0 : Fin 3) ≠ 1 by decide)
        (show (1 : Fin 3) ≠ 2 by decide) (show (0 : Fin 3) ≠ 2 by decide),
      SpecialLinearGroup.transvection_inv]
    congr 1
    simp only [Units.val_neg, Units.val_mul]
    ring
  intro a b hab
  fin_cases a <;> fin_cases b
  · exact absurd rfl hab
  · exact ⟨μ₁, h₁⟩
  · exact ⟨-(μ₁ * μ₃), h02⟩
  · exact ⟨μ₂, h₂⟩
  · exact absurd rfl hab
  · exact ⟨μ₃, h₃⟩
  · exact ⟨-(μ₄ * μ₂), h20⟩
  · exact ⟨μ₄, h₄⟩
  · exact absurd rfl hab

theorem monomial_mul_single_eq {n : ℕ} {W : Matrix (Fin n) (Fin n) L} {π : Equiv.Perm (Fin n)}
    {s : Fin n → L} (hW : ∀ x y, W x y = if x = π y then s y else 0) (hs : ∀ y, s y ≠ 0)
    (a b : Fin n) (c : L) :
    W * single a b c = single (π a) (π b) (s a * c * (s b)⁻¹) * W := by
  ext x y
  simp only [Matrix.mul_apply, Matrix.single_apply, hW]
  rw [Finset.sum_eq_single a (fun z _ hz => by simp [Ne.symm hz]) (by simp),
    Finset.sum_eq_single (π b) (fun z _ hz => by simp [Ne.symm hz]) (by simp)]
  by_cases hx : x = π a <;> by_cases hy : b = y
  · subst hx hy
    simp only [ite_true, and_self]
    field_simp [hs b]
  · simp [hx, hy, (π.injective.ne hy)]
  · simp [hx, Ne.symm hx]
  · simp [hx, Ne.symm hx]

theorem monomial_conj_transvection {n : ℕ} {W : SL(n, L)} {π : Equiv.Perm (Fin n)}
    {s : Fin n → L} (hW : ∀ x y, (W : Matrix (Fin n) (Fin n) L) x y = if x = π y then s y else 0)
    (hs : ∀ y, s y ≠ 0) {a b : Fin n} (hab : a ≠ b) (c : L) :
    W * transvection hab c * W⁻¹ =
      transvection (π.injective.ne hab) (s a * c * (s b)⁻¹) := by
  rw [mul_inv_eq_iff_eq_mul]
  have h : (W : Matrix (Fin n) (Fin n) L) * (1 + single a b c) =
      (1 + single (π a) (π b) (s a * c * (s b)⁻¹)) * W := by
    rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul,
      monomial_mul_single_eq hW hs a b c]
  apply Subtype.ext
  change (W : Matrix (Fin n) (Fin n) L) * (1 + single a b c) =
    (1 + single (π a) (π b) (s a * c * (s b)⁻¹)) * W
  exact h

theorem eq_smul_one_of_commute_sl3_gens {M : Matrix (Fin 3) (Fin 3) L}
    (h1 : M * (1 + single 0 1 1) = (1 + single 0 1 1) * M)
    (h2 : M * (1 + single 1 0 1) = (1 + single 1 0 1) * M)
    (h3 : M * (1 + single 1 2 1) = (1 + single 1 2 1) * M) :
    M = M 0 0 • 1 := by
  have E : ∀ (A : Matrix (Fin 3) (Fin 3) L), M * A = A * M → ∀ i j, (M * A) i j = (A * M) i j :=
    fun A h i j => by rw [h]
  have a01 := E _ h1 0 1
  have a11 := E _ h1 1 1
  have a21 := E _ h1 2 1
  have a02 := E _ h1 0 2
  have b00 := E _ h2 0 0
  have b12 := E _ h2 1 2
  have c12 := E _ h3 1 2
  have c22 := E _ h3 2 2
  simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.single_apply, Matrix.one_apply] at a01 a11
  simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.single_apply, Matrix.one_apply] at a21 a02
  simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.single_apply, Matrix.one_apply] at b00 b12
  simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.single_apply, Matrix.one_apply] at c12 c22
  have e11 : M 1 1 = M 0 0 := by linear_combination -a01
  have e22 : M 2 2 = M 0 0 := by linear_combination -c12 - a01
  ext i j
  fin_cases i <;> fin_cases j <;> simp [a11, a21, a02, b00, b12, c22, e11, e22]

end Transvection

section Weyl

variable (K : Type) [Field K] (κ : F4A2Kind)

@[expose] def f4A2WeylLeft
    : subsystemGroup Tag.F4 K {κ.i, κ.j} :=
  ⟨weylElt Tag.F4 K κ.i 1, weylElt_mem_subsystemGroup (left_mem_pair κ.i κ.j) 1⟩

@[expose] def f4A2WeylRight
    : subsystemGroup Tag.F4 K {κ.i, κ.j} :=
  ⟨weylElt Tag.F4 K κ.j 1, weylElt_mem_subsystemGroup (right_mem_pair κ.i κ.j) 1⟩

theorem f4A2Equiv_weylLeft :
    ((f4A2Equiv K κ (f4A2WeylLeft K κ) : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) =
      !![0, 1, 0; -1, 0, 0; 0, 0, 1] := by
  have hr := isElemRep_f4A2Rep K κ
  rw [f4A2WeylLeft, weylElt_one_eq_prod (left_mem_pair κ.i κ.j), map_mul, map_mul]
  simp only [f4A2Equiv_apply, (hr 1).1, (hr (-1)).2.1]
  change (1 + single 0 1 1 : Matrix (Fin 3) (Fin 3) K) * (1 + single 1 0 (-1)) *
    (1 + single 0 1 1) = _
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.single_apply, Matrix.one_apply]

theorem f4A2Equiv_weylRight :
    ((f4A2Equiv K κ (f4A2WeylRight K κ) : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) =
      !![1, 0, 0; 0, 0, 1; 0, -1, 0] := by
  have hr := isElemRep_f4A2Rep K κ
  rw [f4A2WeylRight, weylElt_one_eq_prod (right_mem_pair κ.i κ.j), map_mul, map_mul]
  simp only [f4A2Equiv_apply, (hr 1).2.2.1, (hr (-1)).2.2.2]
  change (1 + single 1 2 1 : Matrix (Fin 3) (Fin 3) K) * (1 + single 2 1 (-1)) *
    (1 + single 1 2 1) = _
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.single_apply, Matrix.one_apply]

theorem exists_f4A2_weyl_pair
    {δ : ℤ} (hδ : δ = 1 ∨ δ = -1) :
    ∃ v : subsystemGroup Tag.F4 K {κ.i, κ.j}, (v : ModGL Tag.F4 K) ∈ monomialSubgroup Tag.F4 K ∧
      MapsRootLines (v : ModGL Tag.F4 K) ((simple Tag.F4 κ.i * simple Tag.F4 κ.j) ^ δ) ∧
      ∃ (π : Equiv.Perm (Fin 3)) (s : Fin 3 → K), (∀ y, s y ≠ 0) ∧
        ∀ x y, ((f4A2Equiv K κ v : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) x y =
          if x = π y then s y else 0 := by
  rcases hδ with rfl | rfl
  · refine ⟨f4A2WeylLeft K κ * f4A2WeylRight K κ, mul_mem (weylElt_mem_monomialSubgroup _)
      (weylElt_mem_monomialSubgroup _), ?_, finRotate 3, ![-1, -1, 1], ?_, ?_⟩
    · rw [zpow_one]
      exact (mapsRootLines_weylElt κ.i).mul (mapsRootLines_weylElt κ.j)
    · intro y
      fin_cases y <;> simp
    · intro x y
      rw [map_mul]
      change (((f4A2Equiv K κ (f4A2WeylLeft K κ) : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) *
        ((f4A2Equiv K κ (f4A2WeylRight K κ) : SL(3, K)) : Matrix (Fin 3) (Fin 3) K)) x y = _
      rw [f4A2Equiv_weylLeft, f4A2Equiv_weylRight]
      fin_cases x <;> fin_cases y <;> simp [Matrix.mul_apply, Fin.sum_univ_three]
  · refine ⟨f4A2WeylRight K κ * f4A2WeylLeft K κ, mul_mem (weylElt_mem_monomialSubgroup _)
      (weylElt_mem_monomialSubgroup _), ?_, (finRotate 3).symm, ![1, 1, 1], ?_, ?_⟩
    · rw [_root_.zpow_neg_one, _root_.mul_inv_rev, simple_inv, simple_inv]
      exact (mapsRootLines_weylElt κ.j).mul (mapsRootLines_weylElt κ.i)
    · intro y
      fin_cases y <;> simp
    · intro x y
      rw [map_mul]
      change (((f4A2Equiv K κ (f4A2WeylRight K κ) : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) *
        ((f4A2Equiv K κ (f4A2WeylLeft K κ) : SL(3, K)) : Matrix (Fin 3) (Fin 3) K)) x y = _
      rw [f4A2Equiv_weylRight, f4A2Equiv_weylLeft]
      fin_cases x <;> fin_cases y <;> simp [Matrix.mul_apply, Fin.sum_univ_three] <;> decide

end Weyl

theorem blockSL_eq_sl2BlockDiag {L : Type} [Field L] (A : SL(2, L)) :
    (blockSL L 2 1 A : SL(3, L)) = sl2BlockDiag L A := by
  refine Subtype.ext (Matrix.ext fun a b => ?_)
  rw [coe_sl2BlockDiag, CFSG.LocalAnalysis.ComponentInitial.LinearFlag.coe_blockSL,
    CFSG.LocalAnalysis.ComponentInitial.LinearFlag.coe_blockGL]
  fin_cases a <;> fin_cases b <;> rfl

end CFSG.RankThree.Chevalley
