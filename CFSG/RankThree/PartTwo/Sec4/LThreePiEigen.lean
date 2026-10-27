module

public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic.LinearCombination
public import Mathlib.Data.Nat.Totient
public import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition

public section

namespace CFSG.RankThree.PartTwo.Sec4

open Matrix

variable {K : Type} [Field K]

theorem one_add_tau_add_sq {τ : K} (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1) : 1 + τ + τ ^ 2 = 0 := by
  have h : (τ - 1) * (1 + τ + τ ^ 2) = 0 := by linear_combination hτ
  exact (mul_eq_zero.mp h).resolve_left (sub_ne_zero.mpr hτ1)

theorem tau_pow_fin_add {τ : K} (hτ : τ ^ 3 = 1) (a b : Fin 3) :
    τ ^ ((a + b : Fin 3) : ℕ) = τ ^ (a : ℕ) * τ ^ (b : ℕ) := by
  rw [← pow_add, Fin.val_add]
  conv_rhs => rw [← Nat.mod_add_div ((a : ℕ) + b) 3]
  rw [pow_add, pow_mul, hτ, one_pow, mul_one]

@[expose] def eigenProj (τ : K) (y : Matrix (Fin 3) (Fin 3) K) (k : Fin 3) :
    Matrix (Fin 3) (Fin 3) K :=
  (3 : K)⁻¹ • (1 + (τ ^ (k : ℕ)) ^ 2 • y + τ ^ (k : ℕ) • y ^ 2)

theorem mul_eigenProj {τ : K} (hτ : τ ^ 3 = 1) {y : Matrix (Fin 3) (Fin 3) K} (hy : y ^ 3 = 1)
    (k : Fin 3) : y * eigenProj τ y k = τ ^ (k : ℕ) • eigenProj τ y k := by
  have hα : (τ ^ (k : ℕ)) ^ 3 = 1 := by rw [← pow_mul, mul_comm, pow_mul, hτ, one_pow]
  have h2 : y * y = y ^ 2 := (sq y).symm
  have h3' : y * y ^ 2 = 1 := by rw [← pow_succ', hy]
  have hα3 : τ ^ (k : ℕ) * (τ ^ (k : ℕ)) ^ 2 = 1 := by rw [← pow_succ']; exact hα
  unfold eigenProj
  rw [Matrix.mul_smul, smul_comm]
  congr 1
  simp only [Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul, smul_add, smul_smul, h2, h3', hα3,
    one_smul]
  rw [show τ ^ (k : ℕ) * τ ^ (k : ℕ) = (τ ^ (k : ℕ)) ^ 2 by ring]
  abel

theorem sum_eigenProj {τ : K} (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1) (h3 : (3 : K) ≠ 0)
    (y : Matrix (Fin 3) (Fin 3) K) : ∑ k, eigenProj τ y k = 1 := by
  have hs1 := one_add_tau_add_sq hτ hτ1
  have hs2 : 1 + τ ^ 2 + (τ ^ 2) ^ 2 = 0 := by
    have : (τ ^ 2) ^ 2 = τ := by
      rw [← pow_mul]
      calc τ ^ (2 * 2) = τ ^ 3 * τ := by ring
        _ = τ := by rw [hτ, one_mul]
    rw [this]
    linear_combination hs1
  have h3inv : (3 : K)⁻¹ * 3 = 1 := inv_mul_cancel₀ h3
  ext i j
  simp only [eigenProj, Fin.sum_univ_three, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
    Fin.val_zero, Fin.val_one, Fin.val_two, pow_zero, pow_one, one_pow, one_mul]
  linear_combination ((3 : K)⁻¹ * y i j) * hs2 + ((3 : K)⁻¹ * (y ^ 2) i j) * hs1 +
    (1 : Matrix (Fin 3) (Fin 3) K) i j * h3inv

theorem exists_eigenbasis {τ : K} (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1) (h3 : (3 : K) ≠ 0)
    {y : Matrix (Fin 3) (Fin 3) K} (hy : y ^ 3 = 1) :
    ∃ b : Fin 3 → (Fin 3 → K), LinearIndependent K b ∧
      ∀ i, ∃ k : Fin 3, y *ᵥ b i = τ ^ (k : ℕ) • b i := by
  classical
  set S : Set (Fin 3 → K) :=
    Set.range fun kj : Fin 3 × Fin 3 => eigenProj τ y kj.1 *ᵥ Pi.single kj.2 1 with hS
  have hSeig : ∀ w ∈ S, ∃ k : Fin 3, y *ᵥ w = τ ^ (k : ℕ) • w := by
    rintro _ ⟨⟨k, j⟩, rfl⟩
    refine ⟨k, ?_⟩
    rw [Matrix.mulVec_mulVec, mul_eigenProj hτ hy, Matrix.smul_mulVec]
  have hspan : Submodule.span K S = ⊤ := by
    rw [eq_top_iff]
    intro v _
    have hv : v = ∑ j, v j • (Pi.single j (1 : K) : Fin 3 → K) := by
      ext i
      simp [Finset.sum_apply, Pi.single_apply]
    rw [hv]
    refine Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ ?_
    have hj : (Pi.single j (1 : K) : Fin 3 → K) =
        ∑ k, eigenProj τ y k *ᵥ (Pi.single j 1 : Fin 3 → K) := by
      rw [← Matrix.sum_mulVec, sum_eigenProj hτ hτ1 h3, Matrix.one_mulVec]
    rw [hj]
    exact Submodule.sum_mem _ fun k _ => Submodule.subset_span ⟨(k, j), rfl⟩
  obtain ⟨b, hbS, hbspan, hbli⟩ := exists_linearIndependent K S
  have hbtop : ⊤ ≤ Submodule.span K (Set.range ((↑) : b → Fin 3 → K)) := by
    rw [Subtype.range_coe_subtype, Set.ofPred_mem_eq, hbspan, hspan]
  set B := Module.Basis.mk hbli hbtop
  have hfin : Finite b := Module.Finite.finite_basis B
  have : Fintype b := Fintype.ofFinite b
  have hcard : Fintype.card b = 3 := by
    rw [← Module.finrank_eq_card_basis B, Module.finrank_fin_fun]
  set B' := B.reindex (Fintype.equivFinOfCardEq hcard)
  refine ⟨B', B'.linearIndependent, fun i => ?_⟩
  have hmem : B' i ∈ S := by
    rw [Module.Basis.reindex_apply, Module.Basis.mk_apply]
    exact hbS (Subtype.mem _)
  exact hSeig _ hmem

@[expose] def colMat (b : Fin 3 → (Fin 3 → K)) : Matrix (Fin 3) (Fin 3) K :=
  Matrix.of fun r i => b i r

theorem mul_colMat_eq {y : Matrix (Fin 3) (Fin 3) K} {b : Fin 3 → (Fin 3 → K)} {c : Fin 3 → K}
    (h : ∀ i, y *ᵥ b i = c i • b i) : y * colMat b = colMat b * diagonal c := by
  ext r i
  have hi := congrFun (h i) r
  simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at hi
  rw [Matrix.mul_diagonal]
  simp only [Matrix.mul_apply, colMat, of_apply]
  rw [hi, mul_comm]

theorem isUnit_colMat {b : Fin 3 → (Fin 3 → K)} (hb : LinearIndependent K b) :
    IsUnit (colMat b) := by
  rw [← Matrix.linearIndependent_cols_iff_isUnit]
  convert hb using 1
  ext i r
  rfl

theorem exists_perm_shift (k : Fin 3 → Fin 3) (hk : ¬ (k 0 = k 1 ∧ k 1 = k 2)) :
    ∃ σ : Equiv.Perm (Fin 3), ∃ j : Fin 3, (fun i => k (σ i) + j) = ![1, 2, 0] ∨
      (fun i => k (σ i) + j) = ![1, 0, 0] ∨ (fun i => k (σ i) + j) = ![2, 0, 0] := by
  revert k
  decide

theorem exists_normal_form {τ : K} (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1) (h3 : (3 : K) ≠ 0)
    {y : Matrix (Fin 3) (Fin 3) K} (hy : y ^ 3 = 1) (hys : ∀ c : K, y ≠ c • 1) :
    ∃ (g : Matrix (Fin 3) (Fin 3) K) (j : Fin 3), IsUnit g ∧
      ((τ ^ (j : ℕ) • y) * g = g * diagonal ![τ, τ ^ 2, 1] ∨
        (τ ^ (j : ℕ) • y) * g = g * diagonal ![τ, 1, 1] ∨
        (τ ^ (j : ℕ) • y) * g = g * diagonal ![τ ^ 2, 1, 1]) := by
  obtain ⟨b, hb, hk⟩ := exists_eigenbasis hτ hτ1 h3 hy
  choose k hk using hk
  by_cases hconst : k 0 = k 1 ∧ k 1 = k 2
  · exfalso
    apply hys (τ ^ (k 0 : ℕ))
    have hall : ∀ i, y *ᵥ b i = τ ^ (k 0 : ℕ) • b i := by
      intro i
      fin_cases i
      · exact hk 0
      · rw [hconst.1]; exact hk 1
      · rw [hconst.1, hconst.2]; exact hk 2
    have hmul := mul_colMat_eq (c := fun _ => τ ^ (k 0 : ℕ)) hall
    have hu := isUnit_colMat hb
    rw [show (diagonal fun _ : Fin 3 => τ ^ (k 0 : ℕ)) =
      τ ^ (k 0 : ℕ) • (1 : Matrix (Fin 3) (Fin 3) K) by rw [Matrix.smul_one_eq_diagonal],
      Matrix.mul_smul, Matrix.mul_one,
      show τ ^ (k 0 : ℕ) • colMat b = (τ ^ (k 0 : ℕ) • (1 : Matrix (Fin 3) (Fin 3) K)) * colMat b
        by rw [Matrix.smul_mul, Matrix.one_mul]] at hmul
    exact hu.mul_left_inj.mp hmul
  obtain ⟨σ, j, hσj⟩ := exists_perm_shift k hconst
  set b' := b ∘ σ with hb'
  have hb'li : LinearIndependent K b' := hb.comp σ σ.injective
  have hk' : ∀ i, (τ ^ (j : ℕ) • y) *ᵥ b' i = τ ^ ((k (σ i) + j : Fin 3) : ℕ) • b' i := by
    intro i
    rw [Matrix.smul_mulVec, hb', Function.comp_apply, hk, smul_smul, tau_pow_fin_add hτ,
      mul_comm]
  refine ⟨colMat b', j, isUnit_colMat hb'li, ?_⟩
  have hmul := mul_colMat_eq hk'
  have hτ2 : τ ^ ((2 : Fin 3) : ℕ) = τ ^ 2 := rfl
  rcases hσj with h | h | h
  · left
    rw [hmul]
    congr 2
    funext i
    have hi := congrFun h i
    rw [hi]
    fin_cases i <;> simp
  · right; left
    rw [hmul]
    congr 2
    funext i
    have hi := congrFun h i
    rw [hi]
    fin_cases i <;> simp
  · right; right
    rw [hmul]
    congr 2
    funext i
    have hi := congrFun h i
    rw [hi]
    fin_cases i <;> simp

end CFSG.RankThree.PartTwo.Sec4
