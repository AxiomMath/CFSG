module

public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Algebra.CharP.CharAndCard
public import Mathlib.Data.Nat.Prime.Defs

public section

namespace CFSG.StandardType

open scoped CharTwo

def sl3SingerMatrix (K : Type) [Field K] : Matrix (Fin 3) (Fin 3) K :=
  !![0, 0, 1; 1, 0, 1; 0, 1, 0]

def sl3FrobeniusMatrix (K : Type) [Field K] : Matrix (Fin 3) (Fin 3) K :=
  !![1, 0, 0; 0, 0, 1; 0, 1, 1]

lemma sl3SingerMatrix_det (K : Type) [Field K] : (sl3SingerMatrix K).det = 1 := by
  simp [sl3SingerMatrix, Matrix.det_fin_three]

lemma sl3FrobeniusMatrix_det (K : Type) [Field K] [CharP K 2] :
    (sl3FrobeniusMatrix K).det = 1 := by
  simp [sl3FrobeniusMatrix, Matrix.det_fin_three]

lemma sl3FrobeniusMatrix_mul_singer (K : Type) [Field K] [CharP K 2] :
    sl3FrobeniusMatrix K * sl3SingerMatrix K =
      sl3SingerMatrix K ^ 2 * sl3FrobeniusMatrix K := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sl3SingerMatrix, sl3FrobeniusMatrix, Matrix.mul_apply, Fin.sum_univ_three, pow_two]

lemma sl3SingerMatrix_pow_seven (K : Type) [Field K] [CharP K 2] :
    sl3SingerMatrix K ^ 7 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sl3SingerMatrix, Matrix.mul_apply, Fin.sum_univ_three, pow_succ]

def sl3Singer (K : Type) [Field K] : Matrix.SpecialLinearGroup (Fin 3) K :=
  ⟨sl3SingerMatrix K, sl3SingerMatrix_det K⟩

def sl3Frobenius (K : Type) [Field K] [CharP K 2] :
    Matrix.SpecialLinearGroup (Fin 3) K :=
  ⟨sl3FrobeniusMatrix K, sl3FrobeniusMatrix_det K⟩

lemma sl3Singer_orderOf_seven (K : Type) [Field K] [CharP K 2] :
    orderOf (sl3Singer K) = 7 := by
  haveI : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩
  apply orderOf_eq_prime
  · apply Matrix.SpecialLinearGroup.ext
    intro i j
    show (sl3SingerMatrix K ^ 7) i j = (1 : Matrix (Fin 3) (Fin 3) K) i j
    exact congrFun (congrFun (sl3SingerMatrix_pow_seven K) i) j
  · intro h
    have h00 := congrArg (fun A : Matrix.SpecialLinearGroup (Fin 3) K => A 0 0) h
    simp [sl3Singer, sl3SingerMatrix] at h00

lemma sl3Frobenius_conj_singer (K : Type) [Field K] [CharP K 2] :
    sl3Frobenius K * sl3Singer K * (sl3Frobenius K)⁻¹ = (sl3Singer K) ^ 2 := by
  have hns : sl3Frobenius K * sl3Singer K =
      (sl3Singer K) ^ 2 * sl3Frobenius K := by
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    show (sl3FrobeniusMatrix K * sl3SingerMatrix K) i j =
      (sl3SingerMatrix K ^ 2 * sl3FrobeniusMatrix K) i j
    exact congrFun (congrFun (sl3FrobeniusMatrix_mul_singer K) i) j
  calc sl3Frobenius K * sl3Singer K * (sl3Frobenius K)⁻¹
      = ((sl3Singer K) ^ 2 * sl3Frobenius K) * (sl3Frobenius K)⁻¹ := by rw [hns]
    _ = (sl3Singer K) ^ 2 * (sl3Frobenius K * (sl3Frobenius K)⁻¹) := by rw [mul_assoc]
    _ = (sl3Singer K) ^ 2 := by rw [mul_inv_cancel, mul_one]

lemma sl3CenterEqBotOfCardTwo (K : Type) [Field K] [Finite K] (hK : Nat.card K = 2) :
    Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) K) = ⊥ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  letI : Fintype K := Fintype.ofFinite K
  have hcard : Fintype.card K = 2 := by
    rw [Fintype.card_eq_nat_card]
    exact hK
  haveI : CharP K 2 := charP_of_card_eq_prime (p := 2) hcard
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨r, hr3, hr⟩ := (Matrix.SpecialLinearGroup.mem_center_iff (n := Fin 3) (R := K)).mp hx
  have hr3' : r ^ 3 = 1 := by simpa using hr3
  have hr0 : r ≠ 0 := by
    intro h0
    have h01 : (0 : K) = 1 := by simpa [h0] using hr3'
    exact zero_ne_one h01
  have hr1 : r = 1 := by
    obtain ⟨y, _, hyuniq⟩ := (Nat.card_eq_two_iff' (0 : K)).mp hK
    exact (hyuniq r hr0).trans (hyuniq 1 one_ne_zero).symm
  rw [Subgroup.mem_bot]
  apply Subtype.ext
  rw [← hr, hr1]
  exact map_one (Matrix.scalar (Fin 3))

theorem exists_order_seven_frobenius_sl3 {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2) :
    ∃ s n : Matrix.SpecialLinearGroup (Fin 3) K, orderOf s = 7 ∧
      n * s * n⁻¹ = s ^ (2 : ZMod 7).val ∧
      Disjoint (Subgroup.zpowers s) (Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) K)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  letI : Fintype K := Fintype.ofFinite K
  have hcard : Fintype.card K = 2 := by
    rw [Fintype.card_eq_nat_card]
    exact hK
  haveI : CharP K 2 := charP_of_card_eq_prime (p := 2) hcard
  refine ⟨sl3Singer K, sl3Frobenius K, sl3Singer_orderOf_seven K, ?_, ?_⟩
  · have hval : (2 : ZMod 7).val = 2 :=
      ZMod.val_natCast_of_lt (n := 7) (a := 2) (by norm_num)
    rw [hval]
    exact sl3Frobenius_conj_singer K
  · rw [sl3CenterEqBotOfCardTwo K hK]
    exact disjoint_bot_right

end CFSG.StandardType

end
