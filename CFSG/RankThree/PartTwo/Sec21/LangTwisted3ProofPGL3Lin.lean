module

public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.Algebra.CharP.Reduced
import Mathlib.Tactic.LinearCombination

public section

namespace CFSG.RankThree.PartTwo.Sec8.LangTwisted3Proof

open Matrix

variable {K : Type} [Field K]

theorem eq_of_sq_eq_sq_of_charTwo [CharP K 2] {x y : K} (h : x ^ 2 = y ^ 2) : x = y := by
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have : (x - y) ^ 2 = 0 := by linear_combination h + (y ^ 2 - x * y) * h2
  exact sub_eq_zero.mp (pow_eq_zero_iff (by norm_num) |>.mp this)

theorem commute_of_mul_eq_smul [CharP K 2] {S g : Matrix (Fin 3) (Fin 3) K} {ν c : K}
    (hν : ν ≠ 0) (hg : IsUnit g) (hS2 : S * S = ν • 1) (hSg : S * g = c • (g * S)) :
    S * g = g * S := by
  have h1 : S * S * g = (c ^ 2) • (g * (S * S)) := by
    calc S * S * g = S * (S * g) := by rw [Matrix.mul_assoc]
      _ = S * (c • (g * S)) := by rw [hSg]
      _ = c • ((S * g) * S) := by rw [Matrix.mul_smul, Matrix.mul_assoc]
      _ = c • ((c • (g * S)) * S) := by rw [hSg]
      _ = (c ^ 2) • (g * (S * S)) := by
          rw [Matrix.smul_mul, smul_smul, Matrix.mul_assoc, sq]
  rw [hS2, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul, Matrix.mul_one, smul_smul] at h1
  have hne : g ≠ 0 := by
    rintro rfl
    exact not_isUnit_zero hg
  obtain ⟨i, j, hij⟩ : ∃ i j, g i j ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hne (Matrix.ext hcon)
  have h2 := congrFun (congrFun h1 i) j
  simp only [Matrix.smul_apply, smul_eq_mul] at h2
  have hc2 : c ^ 2 = 1 := by
    have : (ν * g i j) * (c ^ 2 - 1) = 0 := by linear_combination -h2
    have h0 : ν * g i j ≠ 0 := mul_ne_zero hν hij
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left h0)
  have hc : c = 1 := eq_of_sq_eq_sq_of_charTwo (by rw [hc2, one_pow])
  rw [hSg, hc, one_smul]

theorem nil_sq_of_sq_eq [CharP K 2] {S : Matrix (Fin 3) (Fin 3) K} {ν r : K}
    (hS2 : S * S = ν • 1) (hr : r * r = ν) : (S + r • 1) * (S + r • 1) = 0 := by
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have e : (S + r • 1) * (S + r • 1) = S * S + (r + r) • S + (r * r) • 1 := by
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
      Matrix.mul_one, smul_add, smul_smul, add_smul]
    abel
  have hrr : r + r = 0 := by linear_combination r * h2
  rw [e, hS2, hrr, zero_smul, add_zero, hr, ← add_smul]
  have hνν : ν + ν = 0 := by linear_combination ν * h2
  rw [hνν, zero_smul]

theorem range_eq_span_of_sq_eq_zero {N : Matrix (Fin 3) (Fin 3) K} (hN : N * N = 0)
    {v : Fin 3 → K} (hv : N *ᵥ v ≠ 0) :
    LinearMap.range (Matrix.toLin' N) = Submodule.span K {N *ᵥ v} := by
  set f := Matrix.toLin' N with hf
  have hle : LinearMap.range f ≤ LinearMap.ker f := by
    rintro _ ⟨u, rfl⟩
    rw [LinearMap.mem_ker, hf, Matrix.toLin'_apply, Matrix.toLin'_apply, Matrix.mulVec_mulVec,
      hN, Matrix.zero_mulVec]
  have hsum := LinearMap.finrank_range_add_finrank_ker f
  rw [Module.finrank_fin_fun] at hsum
  have hmono := Submodule.finrank_mono hle
  have hrk : Module.finrank K (LinearMap.range f) ≤ 1 := by omega
  have hmem : N *ᵥ v ∈ LinearMap.range f := ⟨v, by rw [hf, Matrix.toLin'_apply]⟩
  have hspan : Submodule.span K {N *ᵥ v} ≤ LinearMap.range f :=
    (Submodule.span_singleton_le_iff_mem _ _).2 hmem
  refine (Submodule.eq_of_le_of_finrank_le hspan ?_).symm
  rw [finrank_span_singleton hv]
  exact hrk

theorem exists_eigenvector_of_nil {N g : Matrix (Fin 3) (Fin 3) K} (hN0 : N ≠ 0)
    (hN : N * N = 0) (hNg : N * g = g * N) : ∃ w : Fin 3 → K, w ≠ 0 ∧ ∃ a : K, g *ᵥ w = a • w := by
  obtain ⟨v, hv⟩ : ∃ v : Fin 3 → K, N *ᵥ v ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply hN0
    have : Matrix.toLin' N = 0 := LinearMap.ext fun v => by rw [Matrix.toLin'_apply, hcon v]; rfl
    exact (Matrix.toLin' (R := K) (m := Fin 3) (n := Fin 3)).map_eq_zero_iff.mp this
  refine ⟨N *ᵥ v, hv, ?_⟩
  have hmem : g *ᵥ (N *ᵥ v) ∈ LinearMap.range (Matrix.toLin' N) :=
    ⟨g *ᵥ v, by rw [Matrix.toLin'_apply, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hNg]⟩
  rw [range_eq_span_of_sq_eq_zero hN hv, Submodule.mem_span_singleton] at hmem
  obtain ⟨a, ha⟩ := hmem
  exact ⟨a, ha.symm⟩

theorem exists_eigenvector_of_commute [Finite K] [CharP K 2] {S g : Matrix (Fin 3) (Fin 3) K}
    {ν : K} (hS2 : S * S = ν • 1) (hS : ∀ c : K, S ≠ c • 1) (hSg : S * g = g * S) :
    ∃ w : Fin 3 → K, w ≠ 0 ∧ ∃ a : K, g *ᵥ w = a • w := by
  obtain ⟨r, hr⟩ := isSquare_of_charTwo' ν
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  refine exists_eigenvector_of_nil (N := S + r • 1) ?_ (nil_sq_of_sq_eq hS2 hr.symm) ?_
  · intro h0
    apply hS r
    have : S = -(r • (1 : Matrix (Fin 3) (Fin 3) K)) := eq_neg_of_add_eq_zero_left h0
    rw [this, ← neg_smul]
    congr 1
    linear_combination -r * h2
  · rw [Matrix.add_mul, Matrix.mul_add, hSg, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
      Matrix.mul_one]

theorem eq_smul_one_of_commute_diagonal [CharP K 2] {S y P : Matrix (Fin 3) (Fin 3) K}
    {d : Fin 3 → K} {ν : K} (hP : IsUnit P) (hyP : y * P = P * diagonal d)
    (hd : ∀ i j, i ≠ j → d i ≠ d j) (hSy : S * y = y * S) (hS2 : S * S = ν • 1) :
    ∃ c : K, S = c • 1 := by
  obtain ⟨Pu, rfl⟩ := hP
  set Pm : Matrix (Fin 3) (Fin 3) K := (Pu : Matrix (Fin 3) (Fin 3) K)
  set Pi' : Matrix (Fin 3) (Fin 3) K := ((Pu⁻¹ : (Matrix (Fin 3) (Fin 3) K)ˣ) :
    Matrix (Fin 3) (Fin 3) K)
  have h1 : Pi' * Pm = 1 := Pu.inv_mul
  have h2 : Pm * Pi' = 1 := Pu.mul_inv
  set T := Pi' * S * Pm with hT
  have hy : Pi' * y * Pm = diagonal d := by
    rw [Matrix.mul_assoc, hyP, ← Matrix.mul_assoc, h1, Matrix.one_mul]
  have hTd : T * diagonal d = diagonal d * T := by
    rw [← hy, hT]
    calc Pi' * S * Pm * (Pi' * y * Pm) = Pi' * (S * y) * Pm := by
          simp only [Matrix.mul_assoc]
          rw [← Matrix.mul_assoc Pm Pi', h2, Matrix.one_mul]
      _ = Pi' * (y * S) * Pm := by rw [hSy]
      _ = Pi' * y * Pm * (Pi' * S * Pm) := by
          simp only [Matrix.mul_assoc]
          rw [← Matrix.mul_assoc Pm Pi', h2, Matrix.one_mul]
  have hoff : ∀ i j, i ≠ j → T i j = 0 := by
    intro i j hij
    have := congrFun (congrFun hTd i) j
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul] at this
    have h' : (d j - d i) * T i j = 0 := by linear_combination this
    exact (mul_eq_zero.mp h').resolve_left (sub_ne_zero.mpr (hd j i (Ne.symm hij)))
  have hTT : T * T = ν • 1 := by
    rw [hT]
    calc Pi' * S * Pm * (Pi' * S * Pm) = Pi' * (S * S) * Pm := by
          simp only [Matrix.mul_assoc]
          rw [← Matrix.mul_assoc Pm Pi', h2, Matrix.one_mul]
      _ = ν • 1 := by rw [hS2, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, h1]
  have hdiag : ∀ i, T i i ^ 2 = ν := by
    intro i
    have := congrFun (congrFun hTT i) i
    rw [Matrix.mul_apply, Fin.sum_univ_three] at this
    fin_cases i <;>
      simp [hoff 0 1 (by decide), hoff 0 2 (by decide), hoff 1 0 (by decide),
        hoff 1 2 (by decide), hoff 2 0 (by decide), hoff 2 1 (by decide)] at this ⊢ <;>
      linear_combination this
  have hTc : T = T 0 0 • 1 := by
    ext i j
    rw [Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
    by_cases hij : i = j
    · subst hij
      rw [ite_eq_left rfl, mul_one]
      exact eq_of_sq_eq_sq_of_charTwo (by rw [hdiag i, hdiag 0])
    · rw [ite_eq_right hij, mul_zero, hoff i j hij]
  generalize T 0 0 = c at hTc
  refine ⟨c, ?_⟩
  calc S = Pm * T * Pi' := by
        rw [hT]
        simp only [← Matrix.mul_assoc]
        rw [h2, Matrix.one_mul, Matrix.mul_assoc, h2, Matrix.mul_one]
    _ = c • 1 := by
        rw [hTc, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, h2]

end CFSG.RankThree.PartTwo.Sec8.LangTwisted3Proof
