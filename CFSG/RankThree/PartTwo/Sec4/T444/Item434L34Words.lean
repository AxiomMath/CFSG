module

public import CFSG.Fischer.F4
import all CFSG.Fischer.F4
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.RankThree.PartTwo.Sec4.Item434L34Seitz

open Matrix CFSG.Fischer

variable {K : Type} [Field K]

@[expose] def Ymat (ν : K) : Matrix (Fin 3) (Fin 3) K := !![1, 0, 0; 0, ν, 0; 0, 0, ν * ν]

@[expose] def Xmat (s : K) : Matrix (Fin 3) (Fin 3) K := !![0, 0, s; 1, 0, 0; 0, 1, 0]

@[expose] def genSet (Y X : Matrix (Fin 3) (Fin 3) K) : Set (Matrix.SpecialLinearGroup (Fin 3) K) :=
  {g | Y * g = g * Y ∨ X * g = g * X ∨ X * Y * g = g * (X * Y) ∨
    X * Y * Y * g = g * (X * Y * Y)}

theorem eq_top_of_diagonal_transvection' (H : Subgroup (Matrix.SpecialLinearGroup (Fin 3) K))
    (hdiag : ∀ M : Matrix.SpecialLinearGroup (Fin 3) K,
      (∀ i j, i ≠ j → (M : Matrix (Fin 3) (Fin 3) K) i j = 0) → M ∈ H)
    (htr : ∀ (i j : Fin 3) (hij : i ≠ j) (c : K),
      Matrix.SpecialLinearGroup.transvection hij c ∈ H) :
    H = ⊤ := by
  rw [eq_top_iff]
  intro M _
  refine Matrix.SpecialLinearGroup.diagonal_transvection_induction' (· ∈ H) M ?_ htr
    (fun A B hA hB => H.mul_mem hA hB)
  intro i j hij c hc
  apply hdiag
  intro a b hab
  rw [Matrix.SpecialLinearGroup.diag2n_coe, diagonal_apply_ne _ hab]

theorem mem_genSet_of_diagonal (ν : K) (X : Matrix (Fin 3) (Fin 3) K)
    {M : Matrix.SpecialLinearGroup (Fin 3) K}
    (hM : ∀ i j, i ≠ j → (M : Matrix (Fin 3) (Fin 3) K) i j = 0) : M ∈ genSet (Ymat ν) X := by
  left
  have h01 := hM 0 1 (by decide)
  have h02 := hM 0 2 (by decide)
  have h10 := hM 1 0 (by decide)
  have h12 := hM 1 2 (by decide)
  have h20 := hM 2 0 (by decide)
  have h21 := hM 2 1 (by decide)
  ext k l
  fin_cases k <;> fin_cases l <;>
    simp [Ymat, Matrix.mul_apply, Fin.sum_univ_three, h01, h02, h10, h12, h20, h21, mul_comm]

theorem diag2n_mul_transvection {i j : Fin 3} (hij : i ≠ j) {a : K} (ha : a ≠ 0) (c : K) :
    Matrix.SpecialLinearGroup.diag2n hij a ha * Matrix.SpecialLinearGroup.transvection hij c =
      Matrix.SpecialLinearGroup.transvection hij (a * a * c) *
        Matrix.SpecialLinearGroup.diag2n hij a ha := by
  refine Matrix.SpecialLinearGroup.ext _ _ fun k l => ?_
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.diag2n_coe,
    Matrix.SpecialLinearGroup.transvection_coe, Matrix.add_apply, diagonal_mul, mul_diagonal,
    Matrix.single_apply]
  fin_cases i <;> fin_cases j <;> simp at hij <;> fin_cases k <;> fin_cases l <;> simp <;>
    field_simp

theorem transvection_mem_of_mem {H : Subgroup (Matrix.SpecialLinearGroup (Fin 3) K)}
    (hdiag : ∀ M : Matrix.SpecialLinearGroup (Fin 3) K,
      (∀ i j, i ≠ j → (M : Matrix (Fin 3) (Fin 3) K) i j = 0) → M ∈ H)
    (h4 : ∀ x : K, x ^ 4 = x) {i j : Fin 3} (hij : i ≠ j) {c₀ : K} (hc₀ : c₀ ≠ 0)
    (h : Matrix.SpecialLinearGroup.transvection hij c₀ ∈ H) (c : K) :
    Matrix.SpecialLinearGroup.transvection hij c ∈ H := by
  by_cases hc : c = 0
  · rw [hc, Matrix.SpecialLinearGroup.transvection_coeff_zero]
    exact H.one_mem
  set a := (c / c₀) ^ 2 with ha
  have ha0 : a ≠ 0 := pow_ne_zero _ (div_ne_zero hc hc₀)
  have hD : Matrix.SpecialLinearGroup.diag2n hij a ha0 ∈ H := by
    apply hdiag
    intro k l hkl
    rw [Matrix.SpecialLinearGroup.diag2n_coe, diagonal_apply_ne _ hkl]
  have haa : a * a * c₀ = c := by
    rw [ha, ← pow_add, show 2 + 2 = 4 from rfl, h4, div_mul_cancel₀ _ hc₀]
  have hconj := diag2n_mul_transvection hij ha0 c₀
  rw [haa] at hconj
  have : Matrix.SpecialLinearGroup.transvection hij c =
      Matrix.SpecialLinearGroup.diag2n hij a ha0 * Matrix.SpecialLinearGroup.transvection hij c₀ *
        (Matrix.SpecialLinearGroup.diag2n hij a ha0)⁻¹ := by
    rw [hconj, mul_inv_cancel_right]
  rw [this]
  exact H.mul_mem (H.mul_mem hD h) (H.inv_mem hD)

abbrev fc (k : Fin 4) : F4 := ⟨k⟩

abbrev slF (M : Matrix (Fin 3) (Fin 3) F4) (h : M.det = 1) : Matrix.SpecialLinearGroup (Fin 3) F4 :=
  ⟨M, h⟩

theorem mem_closure_of_word5 {G : Type*} [Group G] {S : Set G} {t : G} (g₁ g₂ g₃ g₄ g₅ : G)
    (h₁ : g₁ ∈ S) (h₂ : g₂ ∈ S) (h₃ : g₃ ∈ S) (h₄ : g₄ ∈ S) (h₅ : g₅ ∈ S)
    (ht : t = g₁ * g₂ * g₃ * g₄ * g₅) : t ∈ Subgroup.closure S := by
  rw [ht]
  exact mul_mem (mul_mem (mul_mem (mul_mem (Subgroup.subset_closure h₁)
    (Subgroup.subset_closure h₂)) (Subgroup.subset_closure h₃)) (Subgroup.subset_closure h₄))
    (Subgroup.subset_closure h₅)

theorem tr_aa_01 : Matrix.SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 1 by decide) (fc 3) ∈
    Subgroup.closure (genSet (Ymat (fc 2)) (Xmat (fc 2))) :=
  mem_closure_of_word5
    (slF !![fc 0, fc 1, fc 1; fc 3, fc 0, fc 1; fc 3, fc 3, fc 0] (by decide))
    (slF !![fc 0, fc 1, fc 1; fc 2, fc 0, fc 2; fc 2, fc 1, fc 0] (by decide))
    (slF !![fc 0, fc 1, fc 1; fc 1, fc 0, fc 3; fc 1, fc 2, fc 0] (by decide))
    (slF !![fc 1, fc 2, fc 2; fc 3, fc 1, fc 3; fc 3, fc 2, fc 1] (by decide))
    (slF !![fc 3, fc 2, fc 2; fc 1, fc 3, fc 2; fc 1, fc 1, fc 3] (by decide))
    (Or.inr <| Or.inl (by decide))
    (Or.inr <| Or.inr <| Or.inr (by decide))
    (Or.inr <| Or.inr <| Or.inl (by decide))
    (Or.inr <| Or.inr <| Or.inr (by decide))
    (Or.inr <| Or.inl (by decide))
    (Subtype.ext (by decide))

theorem tr_aa_02 : Matrix.SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 2 by decide) (fc 3) ∈
    Subgroup.closure (genSet (Ymat (fc 2)) (Xmat (fc 2))) :=
  mem_closure_of_word5
    (slF !![fc 0, fc 1, fc 1; fc 3, fc 0, fc 1; fc 3, fc 3, fc 0] (by decide))
    (slF !![fc 0, fc 1, fc 1; fc 1, fc 0, fc 3; fc 1, fc 2, fc 0] (by decide))
    (slF !![fc 0, fc 1, fc 1; fc 2, fc 0, fc 2; fc 2, fc 1, fc 0] (by decide))
    (slF !![fc 1, fc 1, fc 1; fc 1, fc 1, fc 3; fc 1, fc 2, fc 1] (by decide))
    (slF !![fc 2, fc 1, fc 1; fc 3, fc 2, fc 1; fc 3, fc 3, fc 2] (by decide))
    (Or.inr <| Or.inl (by decide))
    (Or.inr <| Or.inr <| Or.inl (by decide))
    (Or.inr <| Or.inr <| Or.inr (by decide))
    (Or.inr <| Or.inr <| Or.inl (by decide))
    (Or.inr <| Or.inl (by decide))
    (Subtype.ext (by decide))

theorem tr_aa_10 : Matrix.SpecialLinearGroup.transvection (show (1 : Fin 3) ≠ 0 by decide) (fc 2) ∈
    Subgroup.closure (genSet (Ymat (fc 2)) (Xmat (fc 2))) :=
  mem_closure_of_word5
    (slF !![fc 0, fc 1, fc 1; fc 3, fc 0, fc 1; fc 3, fc 3, fc 0] (by decide))
    (slF !![fc 0, fc 1, fc 2; fc 2, fc 0, fc 3; fc 1, fc 3, fc 0] (by decide))
    (slF !![fc 0, fc 1, fc 3; fc 1, fc 0, fc 2; fc 2, fc 3, fc 0] (by decide))
    (slF !![fc 1, fc 2, fc 3; fc 3, fc 1, fc 1; fc 2, fc 1, fc 1] (by decide))
    (slF !![fc 2, fc 1, fc 1; fc 3, fc 2, fc 1; fc 3, fc 3, fc 2] (by decide))
    (Or.inr <| Or.inl (by decide))
    (Or.inr <| Or.inr <| Or.inl (by decide))
    (Or.inr <| Or.inr <| Or.inr (by decide))
    (Or.inr <| Or.inr <| Or.inl (by decide))
    (Or.inr <| Or.inl (by decide))
    (Subtype.ext (by decide))

theorem tr_aa_12 : Matrix.SpecialLinearGroup.transvection (show (1 : Fin 3) ≠ 2 by decide) (fc 3) ∈
    Subgroup.closure (genSet (Ymat (fc 2)) (Xmat (fc 2))) :=
  mem_closure_of_word5
    (slF !![fc 0, fc 1, fc 1; fc 3, fc 0, fc 1; fc 3, fc 3, fc 0] (by decide))
    (slF !![fc 0, fc 1, fc 3; fc 1, fc 0, fc 2; fc 2, fc 3, fc 0] (by decide))
    (slF !![fc 0, fc 1, fc 2; fc 2, fc 0, fc 3; fc 1, fc 3, fc 0] (by decide))
    (slF !![fc 1, fc 1, fc 3; fc 1, fc 1, fc 2; fc 2, fc 3, fc 1] (by decide))
    (slF !![fc 3, fc 2, fc 2; fc 1, fc 3, fc 2; fc 1, fc 1, fc 3] (by decide))
    (Or.inr <| Or.inl (by decide))
    (Or.inr <| Or.inr <| Or.inr (by decide))
    (Or.inr <| Or.inr <| Or.inl (by decide))
    (Or.inr <| Or.inr <| Or.inr (by decide))
    (Or.inr <| Or.inl (by decide))
    (Subtype.ext (by decide))

theorem tr_aa_20 : Matrix.SpecialLinearGroup.transvection (show (2 : Fin 3) ≠ 0 by decide) (fc 2) ∈
    Subgroup.closure (genSet (Ymat (fc 2)) (Xmat (fc 2))) :=
  mem_closure_of_word5
    (slF !![fc 0, fc 1, fc 1; fc 3, fc 0, fc 1; fc 3, fc 3, fc 0] (by decide))
    (slF !![fc 0, fc 1, fc 2; fc 3, fc 0, fc 2; fc 2, fc 2, fc 0] (by decide))
    (slF !![fc 0, fc 1, fc 3; fc 3, fc 0, fc 3; fc 1, fc 1, fc 0] (by decide))
    (slF !![fc 1, fc 3, fc 1; fc 2, fc 1, fc 1; fc 1, fc 1, fc 1] (by decide))
    (slF !![fc 3, fc 2, fc 2; fc 1, fc 3, fc 2; fc 1, fc 1, fc 3] (by decide))
    (Or.inr <| Or.inl (by decide))
    (Or.inr <| Or.inr <| Or.inr (by decide))
    (Or.inr <| Or.inr <| Or.inl (by decide))
    (Or.inr <| Or.inr <| Or.inr (by decide))
    (Or.inr <| Or.inl (by decide))
    (Subtype.ext (by decide))

theorem tr_aa_21 : Matrix.SpecialLinearGroup.transvection (show (2 : Fin 3) ≠ 1 by decide) (fc 2) ∈
    Subgroup.closure (genSet (Ymat (fc 2)) (Xmat (fc 2))) :=
  mem_closure_of_word5
    (slF !![fc 0, fc 1, fc 1; fc 3, fc 0, fc 1; fc 3, fc 3, fc 0] (by decide))
    (slF !![fc 0, fc 1, fc 3; fc 3, fc 0, fc 3; fc 1, fc 1, fc 0] (by decide))
    (slF !![fc 0, fc 1, fc 2; fc 3, fc 0, fc 2; fc 2, fc 2, fc 0] (by decide))
    (slF !![fc 1, fc 3, fc 2; fc 2, fc 1, fc 2; fc 3, fc 3, fc 1] (by decide))
    (slF !![fc 2, fc 1, fc 1; fc 3, fc 2, fc 1; fc 3, fc 3, fc 2] (by decide))
    (Or.inr <| Or.inl (by decide))
    (Or.inr <| Or.inr <| Or.inl (by decide))
    (Or.inr <| Or.inr <| Or.inr (by decide))
    (Or.inr <| Or.inr <| Or.inl (by decide))
    (Or.inr <| Or.inl (by decide))
    (Subtype.ext (by decide))

theorem tr_ab_01 : Matrix.SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 1 by decide) (fc 2) ∈
    Subgroup.closure (genSet (Ymat (fc 2)) (Xmat (fc 3))) :=
  mem_closure_of_word5
    (slF !![fc 0, fc 1, fc 1; fc 2, fc 0, fc 1; fc 2, fc 2, fc 0] (by decide))
    (slF !![fc 0, fc 1, fc 1; fc 3, fc 0, fc 3; fc 3, fc 1, fc 0] (by decide))
    (slF !![fc 0, fc 1, fc 1; fc 1, fc 0, fc 2; fc 1, fc 3, fc 0] (by decide))
    (slF !![fc 1, fc 3, fc 3; fc 2, fc 1, fc 2; fc 2, fc 3, fc 1] (by decide))
    (slF !![fc 2, fc 3, fc 3; fc 1, fc 2, fc 3; fc 1, fc 1, fc 2] (by decide))
    (Or.inr <| Or.inl (by decide))
    (Or.inr <| Or.inr <| Or.inl (by decide))
    (Or.inr <| Or.inr <| Or.inr (by decide))
    (Or.inr <| Or.inr <| Or.inl (by decide))
    (Or.inr <| Or.inl (by decide))
    (Subtype.ext (by decide))

theorem tr_ab_02 : Matrix.SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 2 by decide) (fc 2) ∈
    Subgroup.closure (genSet (Ymat (fc 2)) (Xmat (fc 3))) :=
  mem_closure_of_word5
    (slF !![fc 0, fc 1, fc 1; fc 2, fc 0, fc 1; fc 2, fc 2, fc 0] (by decide))
    (slF !![fc 0, fc 1, fc 1; fc 1, fc 0, fc 2; fc 1, fc 3, fc 0] (by decide))
    (slF !![fc 0, fc 1, fc 1; fc 3, fc 0, fc 3; fc 3, fc 1, fc 0] (by decide))
    (slF !![fc 1, fc 1, fc 1; fc 1, fc 1, fc 2; fc 1, fc 3, fc 1] (by decide))
    (slF !![fc 3, fc 1, fc 1; fc 2, fc 3, fc 1; fc 2, fc 2, fc 3] (by decide))
    (Or.inr <| Or.inl (by decide))
    (Or.inr <| Or.inr <| Or.inr (by decide))
    (Or.inr <| Or.inr <| Or.inl (by decide))
    (Or.inr <| Or.inr <| Or.inr (by decide))
    (Or.inr <| Or.inl (by decide))
    (Subtype.ext (by decide))

theorem tr_ab_10 : Matrix.SpecialLinearGroup.transvection (show (1 : Fin 3) ≠ 0 by decide) (fc 3) ∈
    Subgroup.closure (genSet (Ymat (fc 2)) (Xmat (fc 3))) :=
  mem_closure_of_word5
    (slF !![fc 0, fc 1, fc 1; fc 2, fc 0, fc 1; fc 2, fc 2, fc 0] (by decide))
    (slF !![fc 0, fc 1, fc 3; fc 3, fc 0, fc 2; fc 1, fc 2, fc 0] (by decide))
    (slF !![fc 0, fc 1, fc 2; fc 1, fc 0, fc 3; fc 3, fc 2, fc 0] (by decide))
    (slF !![fc 1, fc 3, fc 2; fc 2, fc 1, fc 1; fc 3, fc 1, fc 1] (by decide))
    (slF !![fc 3, fc 1, fc 1; fc 2, fc 3, fc 1; fc 2, fc 2, fc 3] (by decide))
    (Or.inr <| Or.inl (by decide))
    (Or.inr <| Or.inr <| Or.inr (by decide))
    (Or.inr <| Or.inr <| Or.inl (by decide))
    (Or.inr <| Or.inr <| Or.inr (by decide))
    (Or.inr <| Or.inl (by decide))
    (Subtype.ext (by decide))

theorem tr_ab_12 : Matrix.SpecialLinearGroup.transvection (show (1 : Fin 3) ≠ 2 by decide) (fc 2) ∈
    Subgroup.closure (genSet (Ymat (fc 2)) (Xmat (fc 3))) :=
  mem_closure_of_word5
    (slF !![fc 0, fc 1, fc 1; fc 2, fc 0, fc 1; fc 2, fc 2, fc 0] (by decide))
    (slF !![fc 0, fc 1, fc 2; fc 1, fc 0, fc 3; fc 3, fc 2, fc 0] (by decide))
    (slF !![fc 0, fc 1, fc 3; fc 3, fc 0, fc 2; fc 1, fc 2, fc 0] (by decide))
    (slF !![fc 1, fc 1, fc 2; fc 1, fc 1, fc 3; fc 3, fc 2, fc 1] (by decide))
    (slF !![fc 2, fc 3, fc 3; fc 1, fc 2, fc 3; fc 1, fc 1, fc 2] (by decide))
    (Or.inr <| Or.inl (by decide))
    (Or.inr <| Or.inr <| Or.inl (by decide))
    (Or.inr <| Or.inr <| Or.inr (by decide))
    (Or.inr <| Or.inr <| Or.inl (by decide))
    (Or.inr <| Or.inl (by decide))
    (Subtype.ext (by decide))

theorem tr_ab_20 : Matrix.SpecialLinearGroup.transvection (show (2 : Fin 3) ≠ 0 by decide) (fc 3) ∈
    Subgroup.closure (genSet (Ymat (fc 2)) (Xmat (fc 3))) :=
  mem_closure_of_word5
    (slF !![fc 0, fc 1, fc 1; fc 2, fc 0, fc 1; fc 2, fc 2, fc 0] (by decide))
    (slF !![fc 0, fc 1, fc 3; fc 2, fc 0, fc 3; fc 3, fc 3, fc 0] (by decide))
    (slF !![fc 0, fc 1, fc 2; fc 2, fc 0, fc 2; fc 1, fc 1, fc 0] (by decide))
    (slF !![fc 1, fc 2, fc 1; fc 3, fc 1, fc 1; fc 1, fc 1, fc 1] (by decide))
    (slF !![fc 2, fc 3, fc 3; fc 1, fc 2, fc 3; fc 1, fc 1, fc 2] (by decide))
    (Or.inr <| Or.inl (by decide))
    (Or.inr <| Or.inr <| Or.inl (by decide))
    (Or.inr <| Or.inr <| Or.inr (by decide))
    (Or.inr <| Or.inr <| Or.inl (by decide))
    (Or.inr <| Or.inl (by decide))
    (Subtype.ext (by decide))

theorem tr_ab_21 : Matrix.SpecialLinearGroup.transvection (show (2 : Fin 3) ≠ 1 by decide) (fc 3) ∈
    Subgroup.closure (genSet (Ymat (fc 2)) (Xmat (fc 3))) :=
  mem_closure_of_word5
    (slF !![fc 0, fc 1, fc 1; fc 2, fc 0, fc 1; fc 2, fc 2, fc 0] (by decide))
    (slF !![fc 0, fc 1, fc 2; fc 2, fc 0, fc 2; fc 1, fc 1, fc 0] (by decide))
    (slF !![fc 0, fc 1, fc 3; fc 2, fc 0, fc 3; fc 3, fc 3, fc 0] (by decide))
    (slF !![fc 1, fc 2, fc 3; fc 3, fc 1, fc 3; fc 2, fc 2, fc 1] (by decide))
    (slF !![fc 3, fc 1, fc 1; fc 2, fc 3, fc 1; fc 2, fc 2, fc 3] (by decide))
    (Or.inr <| Or.inl (by decide))
    (Or.inr <| Or.inr <| Or.inr (by decide))
    (Or.inr <| Or.inr <| Or.inl (by decide))
    (Or.inr <| Or.inr <| Or.inr (by decide))
    (Or.inr <| Or.inl (by decide))
    (Subtype.ext (by decide))

theorem tr_ba_01 : Matrix.SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 1 by decide) (fc 3) ∈
    Subgroup.closure (genSet (Ymat (fc 3)) (Xmat (fc 2))) :=
  mem_closure_of_word5
    (slF !![fc 0, fc 1, fc 1; fc 3, fc 0, fc 1; fc 3, fc 3, fc 0] (by decide))
    (slF !![fc 0, fc 1, fc 1; fc 2, fc 0, fc 2; fc 2, fc 1, fc 0] (by decide))
    (slF !![fc 0, fc 1, fc 1; fc 1, fc 0, fc 3; fc 1, fc 2, fc 0] (by decide))
    (slF !![fc 1, fc 2, fc 2; fc 3, fc 1, fc 3; fc 3, fc 2, fc 1] (by decide))
    (slF !![fc 3, fc 2, fc 2; fc 1, fc 3, fc 2; fc 1, fc 1, fc 3] (by decide))
    (Or.inr <| Or.inl (by decide))
    (Or.inr <| Or.inr <| Or.inl (by decide))
    (Or.inr <| Or.inr <| Or.inr (by decide))
    (Or.inr <| Or.inr <| Or.inl (by decide))
    (Or.inr <| Or.inl (by decide))
    (Subtype.ext (by decide))

theorem tr_ba_02 : Matrix.SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 2 by decide) (fc 3) ∈
    Subgroup.closure (genSet (Ymat (fc 3)) (Xmat (fc 2))) :=
  mem_closure_of_word5
    (slF !![fc 0, fc 1, fc 1; fc 3, fc 0, fc 1; fc 3, fc 3, fc 0] (by decide))
    (slF !![fc 0, fc 1, fc 1; fc 1, fc 0, fc 3; fc 1, fc 2, fc 0] (by decide))
    (slF !![fc 0, fc 1, fc 1; fc 2, fc 0, fc 2; fc 2, fc 1, fc 0] (by decide))
    (slF !![fc 1, fc 1, fc 1; fc 1, fc 1, fc 3; fc 1, fc 2, fc 1] (by decide))
    (slF !![fc 2, fc 1, fc 1; fc 3, fc 2, fc 1; fc 3, fc 3, fc 2] (by decide))
    (Or.inr <| Or.inl (by decide))
    (Or.inr <| Or.inr <| Or.inr (by decide))
    (Or.inr <| Or.inr <| Or.inl (by decide))
    (Or.inr <| Or.inr <| Or.inr (by decide))
    (Or.inr <| Or.inl (by decide))
    (Subtype.ext (by decide))

theorem tr_ba_10 : Matrix.SpecialLinearGroup.transvection (show (1 : Fin 3) ≠ 0 by decide) (fc 2) ∈
    Subgroup.closure (genSet (Ymat (fc 3)) (Xmat (fc 2))) :=
  mem_closure_of_word5
    (slF !![fc 0, fc 1, fc 1; fc 3, fc 0, fc 1; fc 3, fc 3, fc 0] (by decide))
    (slF !![fc 0, fc 1, fc 2; fc 2, fc 0, fc 3; fc 1, fc 3, fc 0] (by decide))
    (slF !![fc 0, fc 1, fc 3; fc 1, fc 0, fc 2; fc 2, fc 3, fc 0] (by decide))
    (slF !![fc 1, fc 2, fc 3; fc 3, fc 1, fc 1; fc 2, fc 1, fc 1] (by decide))
    (slF !![fc 2, fc 1, fc 1; fc 3, fc 2, fc 1; fc 3, fc 3, fc 2] (by decide))
    (Or.inr <| Or.inl (by decide))
    (Or.inr <| Or.inr <| Or.inr (by decide))
    (Or.inr <| Or.inr <| Or.inl (by decide))
    (Or.inr <| Or.inr <| Or.inr (by decide))
    (Or.inr <| Or.inl (by decide))
    (Subtype.ext (by decide))

theorem tr_ba_12 : Matrix.SpecialLinearGroup.transvection (show (1 : Fin 3) ≠ 2 by decide) (fc 3) ∈
    Subgroup.closure (genSet (Ymat (fc 3)) (Xmat (fc 2))) :=
  mem_closure_of_word5
    (slF !![fc 0, fc 1, fc 1; fc 3, fc 0, fc 1; fc 3, fc 3, fc 0] (by decide))
    (slF !![fc 0, fc 1, fc 3; fc 1, fc 0, fc 2; fc 2, fc 3, fc 0] (by decide))
    (slF !![fc 0, fc 1, fc 2; fc 2, fc 0, fc 3; fc 1, fc 3, fc 0] (by decide))
    (slF !![fc 1, fc 1, fc 3; fc 1, fc 1, fc 2; fc 2, fc 3, fc 1] (by decide))
    (slF !![fc 3, fc 2, fc 2; fc 1, fc 3, fc 2; fc 1, fc 1, fc 3] (by decide))
    (Or.inr <| Or.inl (by decide))
    (Or.inr <| Or.inr <| Or.inl (by decide))
    (Or.inr <| Or.inr <| Or.inr (by decide))
    (Or.inr <| Or.inr <| Or.inl (by decide))
    (Or.inr <| Or.inl (by decide))
    (Subtype.ext (by decide))

theorem tr_ba_20 : Matrix.SpecialLinearGroup.transvection (show (2 : Fin 3) ≠ 0 by decide) (fc 2) ∈
    Subgroup.closure (genSet (Ymat (fc 3)) (Xmat (fc 2))) :=
  mem_closure_of_word5
    (slF !![fc 0, fc 1, fc 1; fc 3, fc 0, fc 1; fc 3, fc 3, fc 0] (by decide))
    (slF !![fc 0, fc 1, fc 2; fc 3, fc 0, fc 2; fc 2, fc 2, fc 0] (by decide))
    (slF !![fc 0, fc 1, fc 3; fc 3, fc 0, fc 3; fc 1, fc 1, fc 0] (by decide))
    (slF !![fc 1, fc 3, fc 1; fc 2, fc 1, fc 1; fc 1, fc 1, fc 1] (by decide))
    (slF !![fc 3, fc 2, fc 2; fc 1, fc 3, fc 2; fc 1, fc 1, fc 3] (by decide))
    (Or.inr <| Or.inl (by decide))
    (Or.inr <| Or.inr <| Or.inl (by decide))
    (Or.inr <| Or.inr <| Or.inr (by decide))
    (Or.inr <| Or.inr <| Or.inl (by decide))
    (Or.inr <| Or.inl (by decide))
    (Subtype.ext (by decide))

theorem tr_ba_21 : Matrix.SpecialLinearGroup.transvection (show (2 : Fin 3) ≠ 1 by decide) (fc 2) ∈
    Subgroup.closure (genSet (Ymat (fc 3)) (Xmat (fc 2))) :=
  mem_closure_of_word5
    (slF !![fc 0, fc 1, fc 1; fc 3, fc 0, fc 1; fc 3, fc 3, fc 0] (by decide))
    (slF !![fc 0, fc 1, fc 3; fc 3, fc 0, fc 3; fc 1, fc 1, fc 0] (by decide))
    (slF !![fc 0, fc 1, fc 2; fc 3, fc 0, fc 2; fc 2, fc 2, fc 0] (by decide))
    (slF !![fc 1, fc 3, fc 2; fc 2, fc 1, fc 2; fc 3, fc 3, fc 1] (by decide))
    (slF !![fc 2, fc 1, fc 1; fc 3, fc 2, fc 1; fc 3, fc 3, fc 2] (by decide))
    (Or.inr <| Or.inl (by decide))
    (Or.inr <| Or.inr <| Or.inr (by decide))
    (Or.inr <| Or.inr <| Or.inl (by decide))
    (Or.inr <| Or.inr <| Or.inr (by decide))
    (Or.inr <| Or.inl (by decide))
    (Subtype.ext (by decide))

theorem tr_bb_01 : Matrix.SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 1 by decide) (fc 2) ∈
    Subgroup.closure (genSet (Ymat (fc 3)) (Xmat (fc 3))) :=
  mem_closure_of_word5
    (slF !![fc 0, fc 1, fc 1; fc 2, fc 0, fc 1; fc 2, fc 2, fc 0] (by decide))
    (slF !![fc 0, fc 1, fc 1; fc 3, fc 0, fc 3; fc 3, fc 1, fc 0] (by decide))
    (slF !![fc 0, fc 1, fc 1; fc 1, fc 0, fc 2; fc 1, fc 3, fc 0] (by decide))
    (slF !![fc 1, fc 3, fc 3; fc 2, fc 1, fc 2; fc 2, fc 3, fc 1] (by decide))
    (slF !![fc 2, fc 3, fc 3; fc 1, fc 2, fc 3; fc 1, fc 1, fc 2] (by decide))
    (Or.inr <| Or.inl (by decide))
    (Or.inr <| Or.inr <| Or.inr (by decide))
    (Or.inr <| Or.inr <| Or.inl (by decide))
    (Or.inr <| Or.inr <| Or.inr (by decide))
    (Or.inr <| Or.inl (by decide))
    (Subtype.ext (by decide))

theorem tr_bb_02 : Matrix.SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 2 by decide) (fc 2) ∈
    Subgroup.closure (genSet (Ymat (fc 3)) (Xmat (fc 3))) :=
  mem_closure_of_word5
    (slF !![fc 0, fc 1, fc 1; fc 2, fc 0, fc 1; fc 2, fc 2, fc 0] (by decide))
    (slF !![fc 0, fc 1, fc 1; fc 1, fc 0, fc 2; fc 1, fc 3, fc 0] (by decide))
    (slF !![fc 0, fc 1, fc 1; fc 3, fc 0, fc 3; fc 3, fc 1, fc 0] (by decide))
    (slF !![fc 1, fc 1, fc 1; fc 1, fc 1, fc 2; fc 1, fc 3, fc 1] (by decide))
    (slF !![fc 3, fc 1, fc 1; fc 2, fc 3, fc 1; fc 2, fc 2, fc 3] (by decide))
    (Or.inr <| Or.inl (by decide))
    (Or.inr <| Or.inr <| Or.inl (by decide))
    (Or.inr <| Or.inr <| Or.inr (by decide))
    (Or.inr <| Or.inr <| Or.inl (by decide))
    (Or.inr <| Or.inl (by decide))
    (Subtype.ext (by decide))

theorem tr_bb_10 : Matrix.SpecialLinearGroup.transvection (show (1 : Fin 3) ≠ 0 by decide) (fc 3) ∈
    Subgroup.closure (genSet (Ymat (fc 3)) (Xmat (fc 3))) :=
  mem_closure_of_word5
    (slF !![fc 0, fc 1, fc 1; fc 2, fc 0, fc 1; fc 2, fc 2, fc 0] (by decide))
    (slF !![fc 0, fc 1, fc 3; fc 3, fc 0, fc 2; fc 1, fc 2, fc 0] (by decide))
    (slF !![fc 0, fc 1, fc 2; fc 1, fc 0, fc 3; fc 3, fc 2, fc 0] (by decide))
    (slF !![fc 1, fc 3, fc 2; fc 2, fc 1, fc 1; fc 3, fc 1, fc 1] (by decide))
    (slF !![fc 3, fc 1, fc 1; fc 2, fc 3, fc 1; fc 2, fc 2, fc 3] (by decide))
    (Or.inr <| Or.inl (by decide))
    (Or.inr <| Or.inr <| Or.inl (by decide))
    (Or.inr <| Or.inr <| Or.inr (by decide))
    (Or.inr <| Or.inr <| Or.inl (by decide))
    (Or.inr <| Or.inl (by decide))
    (Subtype.ext (by decide))

theorem tr_bb_12 : Matrix.SpecialLinearGroup.transvection (show (1 : Fin 3) ≠ 2 by decide) (fc 2) ∈
    Subgroup.closure (genSet (Ymat (fc 3)) (Xmat (fc 3))) :=
  mem_closure_of_word5
    (slF !![fc 0, fc 1, fc 1; fc 2, fc 0, fc 1; fc 2, fc 2, fc 0] (by decide))
    (slF !![fc 0, fc 1, fc 2; fc 1, fc 0, fc 3; fc 3, fc 2, fc 0] (by decide))
    (slF !![fc 0, fc 1, fc 3; fc 3, fc 0, fc 2; fc 1, fc 2, fc 0] (by decide))
    (slF !![fc 1, fc 1, fc 2; fc 1, fc 1, fc 3; fc 3, fc 2, fc 1] (by decide))
    (slF !![fc 2, fc 3, fc 3; fc 1, fc 2, fc 3; fc 1, fc 1, fc 2] (by decide))
    (Or.inr <| Or.inl (by decide))
    (Or.inr <| Or.inr <| Or.inr (by decide))
    (Or.inr <| Or.inr <| Or.inl (by decide))
    (Or.inr <| Or.inr <| Or.inr (by decide))
    (Or.inr <| Or.inl (by decide))
    (Subtype.ext (by decide))

theorem tr_bb_20 : Matrix.SpecialLinearGroup.transvection (show (2 : Fin 3) ≠ 0 by decide) (fc 3) ∈
    Subgroup.closure (genSet (Ymat (fc 3)) (Xmat (fc 3))) :=
  mem_closure_of_word5
    (slF !![fc 0, fc 1, fc 1; fc 2, fc 0, fc 1; fc 2, fc 2, fc 0] (by decide))
    (slF !![fc 0, fc 1, fc 3; fc 2, fc 0, fc 3; fc 3, fc 3, fc 0] (by decide))
    (slF !![fc 0, fc 1, fc 2; fc 2, fc 0, fc 2; fc 1, fc 1, fc 0] (by decide))
    (slF !![fc 1, fc 2, fc 1; fc 3, fc 1, fc 1; fc 1, fc 1, fc 1] (by decide))
    (slF !![fc 2, fc 3, fc 3; fc 1, fc 2, fc 3; fc 1, fc 1, fc 2] (by decide))
    (Or.inr <| Or.inl (by decide))
    (Or.inr <| Or.inr <| Or.inr (by decide))
    (Or.inr <| Or.inr <| Or.inl (by decide))
    (Or.inr <| Or.inr <| Or.inr (by decide))
    (Or.inr <| Or.inl (by decide))
    (Subtype.ext (by decide))

theorem tr_bb_21 : Matrix.SpecialLinearGroup.transvection (show (2 : Fin 3) ≠ 1 by decide) (fc 3) ∈
    Subgroup.closure (genSet (Ymat (fc 3)) (Xmat (fc 3))) :=
  mem_closure_of_word5
    (slF !![fc 0, fc 1, fc 1; fc 2, fc 0, fc 1; fc 2, fc 2, fc 0] (by decide))
    (slF !![fc 0, fc 1, fc 2; fc 2, fc 0, fc 2; fc 1, fc 1, fc 0] (by decide))
    (slF !![fc 0, fc 1, fc 3; fc 2, fc 0, fc 3; fc 3, fc 3, fc 0] (by decide))
    (slF !![fc 1, fc 2, fc 3; fc 3, fc 1, fc 3; fc 2, fc 2, fc 1] (by decide))
    (slF !![fc 3, fc 1, fc 1; fc 2, fc 3, fc 1; fc 2, fc 2, fc 3] (by decide))
    (Or.inr <| Or.inl (by decide))
    (Or.inr <| Or.inr <| Or.inl (by decide))
    (Or.inr <| Or.inr <| Or.inr (by decide))
    (Or.inr <| Or.inr <| Or.inl (by decide))
    (Or.inr <| Or.inl (by decide))
    (Subtype.ext (by decide))

theorem key_aa (i j : Fin 3) (hij : i ≠ j) : ∃ c₀ : F4, c₀ ≠ 0 ∧
    Matrix.SpecialLinearGroup.transvection hij c₀ ∈
      Subgroup.closure (genSet (Ymat (fc 2)) (Xmat (fc 2))) := by
  fin_cases i <;> fin_cases j
  · exact absurd rfl hij
  · exact ⟨fc 3, by decide, tr_aa_01⟩
  · exact ⟨fc 3, by decide, tr_aa_02⟩
  · exact ⟨fc 2, by decide, tr_aa_10⟩
  · exact absurd rfl hij
  · exact ⟨fc 3, by decide, tr_aa_12⟩
  · exact ⟨fc 2, by decide, tr_aa_20⟩
  · exact ⟨fc 2, by decide, tr_aa_21⟩
  · exact absurd rfl hij

theorem key_ab (i j : Fin 3) (hij : i ≠ j) : ∃ c₀ : F4, c₀ ≠ 0 ∧
    Matrix.SpecialLinearGroup.transvection hij c₀ ∈
      Subgroup.closure (genSet (Ymat (fc 2)) (Xmat (fc 3))) := by
  fin_cases i <;> fin_cases j
  · exact absurd rfl hij
  · exact ⟨fc 2, by decide, tr_ab_01⟩
  · exact ⟨fc 2, by decide, tr_ab_02⟩
  · exact ⟨fc 3, by decide, tr_ab_10⟩
  · exact absurd rfl hij
  · exact ⟨fc 2, by decide, tr_ab_12⟩
  · exact ⟨fc 3, by decide, tr_ab_20⟩
  · exact ⟨fc 3, by decide, tr_ab_21⟩
  · exact absurd rfl hij

theorem key_ba (i j : Fin 3) (hij : i ≠ j) : ∃ c₀ : F4, c₀ ≠ 0 ∧
    Matrix.SpecialLinearGroup.transvection hij c₀ ∈
      Subgroup.closure (genSet (Ymat (fc 3)) (Xmat (fc 2))) := by
  fin_cases i <;> fin_cases j
  · exact absurd rfl hij
  · exact ⟨fc 3, by decide, tr_ba_01⟩
  · exact ⟨fc 3, by decide, tr_ba_02⟩
  · exact ⟨fc 2, by decide, tr_ba_10⟩
  · exact absurd rfl hij
  · exact ⟨fc 3, by decide, tr_ba_12⟩
  · exact ⟨fc 2, by decide, tr_ba_20⟩
  · exact ⟨fc 2, by decide, tr_ba_21⟩
  · exact absurd rfl hij

theorem key_bb (i j : Fin 3) (hij : i ≠ j) : ∃ c₀ : F4, c₀ ≠ 0 ∧
    Matrix.SpecialLinearGroup.transvection hij c₀ ∈
      Subgroup.closure (genSet (Ymat (fc 3)) (Xmat (fc 3))) := by
  fin_cases i <;> fin_cases j
  · exact absurd rfl hij
  · exact ⟨fc 2, by decide, tr_bb_01⟩
  · exact ⟨fc 2, by decide, tr_bb_02⟩
  · exact ⟨fc 3, by decide, tr_bb_10⟩
  · exact absurd rfl hij
  · exact ⟨fc 2, by decide, tr_bb_12⟩
  · exact ⟨fc 3, by decide, tr_bb_20⟩
  · exact ⟨fc 3, by decide, tr_bb_21⟩
  · exact absurd rfl hij

theorem closure_genSet_eq_top_F4 {ν s : F4} (hν : ν = fc 2 ∨ ν = fc 3) (hs : s = fc 2 ∨ s = fc 3) :
    Subgroup.closure (genSet (Ymat ν) (Xmat s)) = ⊤ := by
  have h4 : ∀ x : F4, x ^ 4 = x := by decide
  have hdiag : ∀ M : Matrix.SpecialLinearGroup (Fin 3) F4,
      (∀ i j, i ≠ j → (M : Matrix (Fin 3) (Fin 3) F4) i j = 0) →
        M ∈ Subgroup.closure (genSet (Ymat ν) (Xmat s)) := fun M hM =>
    Subgroup.subset_closure (mem_genSet_of_diagonal _ _ hM)
  have key : ∀ (i j : Fin 3) (hij : i ≠ j), ∃ c₀ : F4, c₀ ≠ 0 ∧
      Matrix.SpecialLinearGroup.transvection hij c₀ ∈
        Subgroup.closure (genSet (Ymat ν) (Xmat s)) := by
    rcases hν with rfl | rfl <;> rcases hs with rfl | rfl
    · exact key_aa
    · exact key_ab
    · exact key_ba
    · exact key_bb
  apply eq_top_of_diagonal_transvection' _ hdiag
  intro i j hij c
  obtain ⟨c₀, hc₀, h⟩ := key i j hij
  exact transvection_mem_of_mem hdiag h4 hij hc₀ h c

end CFSG.RankThree.PartTwo.Sec4.Item434L34Seitz
