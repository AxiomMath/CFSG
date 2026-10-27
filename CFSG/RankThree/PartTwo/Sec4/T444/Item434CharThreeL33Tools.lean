module

public import CFSG.RankThree.PartTwo.Sec4.T444.Item434CharThreeL3Tools
import CFSG.RankThree.PartTwo.Sec5.Tools
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434Kit

public section

namespace CFSG.RankThree.PartTwo.Sec4.Item434CharThree

open CFSG Matrix
open CFSG.SectionRank.OddCover (u3Mat)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open scoped MatrixGroups

section Centralizers

variable {K : Type} [Field K]

theorem mul_u3Mat_apply (W : Matrix (Fin 3) (Fin 3) K) (a b c : K) (i : Fin 3) :
    (W * u3Mat a b c) i 0 = W i 0 ∧ (W * u3Mat a b c) i 1 = W i 0 * a + W i 1 ∧
      (W * u3Mat a b c) i 2 = W i 0 * c + W i 1 * b + W i 2 := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [Matrix.mul_apply, Fin.sum_univ_three, u3Mat]

theorem u3Mat_mul_apply (W : Matrix (Fin 3) (Fin 3) K) (a b c : K) (j : Fin 3) :
    (u3Mat a b c * W) 0 j = W 0 j + a * W 1 j + c * W 2 j ∧
      (u3Mat a b c * W) 1 j = W 1 j + b * W 2 j ∧ (u3Mat a b c * W) 2 j = W 2 j := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [Matrix.mul_apply, Fin.sum_univ_three, u3Mat]

theorem mul_apply_three (M W : Matrix (Fin 3) (Fin 3) K) (i j : Fin 3) :
    (M * W) i j = M i 0 * W 0 j + M i 1 * W 1 j + M i 2 * W 2 j := by
  rw [Matrix.mul_apply, Fin.sum_univ_three]

theorem entries_of_commute {w : SL(3, K)} {a b c : K} (h : w * uSL a b c = uSL a b c * w)
    (i j : Fin 3) :
    ((w : Matrix (Fin 3) (Fin 3) K) * u3Mat a b c) i j =
      (u3Mat a b c * (w : Matrix (Fin 3) (Fin 3) K)) i j :=
  congrFun (congrFun (congrArg Subtype.val h) i) j

theorem ut_of_commute_z {w : SL(3, K)} {c : K} (hc : c ≠ 0)
    (h : w * uSL 0 0 c = uSL 0 0 c * w) :
    (w : Matrix (Fin 3) (Fin 3) K) 1 0 = 0 ∧ (w : Matrix (Fin 3) (Fin 3) K) 2 0 = 0 ∧
      (w : Matrix (Fin 3) (Fin 3) K) 2 1 = 0 ∧
        (w : Matrix (Fin 3) (Fin 3) K) 0 0 = (w : Matrix (Fin 3) (Fin 3) K) 2 2 := by
  set W := (w : Matrix (Fin 3) (Fin 3) K) with hW
  have e12 := entries_of_commute h 1 2
  have e22 := entries_of_commute h 2 2
  have e01 := entries_of_commute h 0 1
  have e02 := entries_of_commute h 0 2
  rw [(mul_u3Mat_apply W 0 0 c 1).2.2, (u3Mat_mul_apply W 0 0 c 2).2.1] at e12
  rw [(mul_u3Mat_apply W 0 0 c 2).2.2, (u3Mat_mul_apply W 0 0 c 2).2.2] at e22
  rw [(mul_u3Mat_apply W 0 0 c 0).2.1, (u3Mat_mul_apply W 0 0 c 1).1] at e01
  rw [(mul_u3Mat_apply W 0 0 c 0).2.2, (u3Mat_mul_apply W 0 0 c 2).1] at e02
  have h10 : W 1 0 = 0 := by
    have : W 1 0 * c = 0 := by linear_combination e12
    exact (mul_eq_zero.mp this).resolve_right hc
  have h20 : W 2 0 = 0 := by
    have : W 2 0 * c = 0 := by linear_combination e22
    exact (mul_eq_zero.mp this).resolve_right hc
  have h21 : W 2 1 = 0 := by
    have : c * W 2 1 = 0 := by linear_combination -e01
    exact (mul_eq_zero.mp this).resolve_left hc
  have h0022 : W 0 0 = W 2 2 := by
    have : c * (W 0 0 - W 2 2) = 0 := by linear_combination e02
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left hc)
  exact ⟨h10, h20, h21, h0022⟩

theorem ut_of_commute_regular {w : SL(3, K)} {a b c : K} (ha : a ≠ 0) (hb : b ≠ 0)
    (h : w * uSL a b c = uSL a b c * w) :
    (w : Matrix (Fin 3) (Fin 3) K) 1 0 = 0 ∧ (w : Matrix (Fin 3) (Fin 3) K) 2 0 = 0 ∧
      (w : Matrix (Fin 3) (Fin 3) K) 2 1 = 0 := by
  set W := (w : Matrix (Fin 3) (Fin 3) K) with hW
  have e21 := entries_of_commute h 2 1
  have e22 := entries_of_commute h 2 2
  have e11 := entries_of_commute h 1 1
  rw [(mul_u3Mat_apply W a b c 2).2.1, (u3Mat_mul_apply W a b c 1).2.2] at e21
  rw [(mul_u3Mat_apply W a b c 2).2.2, (u3Mat_mul_apply W a b c 2).2.2] at e22
  rw [(mul_u3Mat_apply W a b c 1).2.1, (u3Mat_mul_apply W a b c 1).2.1] at e11
  have h20 : W 2 0 = 0 := by
    have : W 2 0 * a = 0 := by linear_combination e21
    exact (mul_eq_zero.mp this).resolve_right ha
  have h21 : W 2 1 = 0 := by
    have : W 2 1 * b = 0 := by linear_combination e22 - c * h20
    exact (mul_eq_zero.mp this).resolve_right hb
  have h10 : W 1 0 = 0 := by
    have : W 1 0 * a = 0 := by linear_combination e11 + b * h21
    exact (mul_eq_zero.mp this).resolve_right ha
  exact ⟨h10, h20, h21⟩

theorem p1_of_commute {w : SL(3, K)} {a c : K} (ha : a ≠ 0) (h : w * uSL a 0 c = uSL a 0 c * w) :
    (w : Matrix (Fin 3) (Fin 3) K) 1 0 = 0 ∧ (w : Matrix (Fin 3) (Fin 3) K) 2 0 = 0 := by
  set W := (w : Matrix (Fin 3) (Fin 3) K) with hW
  have e11 := entries_of_commute h 1 1
  have e21 := entries_of_commute h 2 1
  rw [(mul_u3Mat_apply W a 0 c 1).2.1, (u3Mat_mul_apply W a 0 c 1).2.1] at e11
  rw [(mul_u3Mat_apply W a 0 c 2).2.1, (u3Mat_mul_apply W a 0 c 1).2.2] at e21
  have h10 : W 1 0 = 0 := by
    have : W 1 0 * a = 0 := by linear_combination e11
    exact (mul_eq_zero.mp this).resolve_right ha
  have h20 : W 2 0 = 0 := by
    have : W 2 0 * a = 0 := by linear_combination e21
    exact (mul_eq_zero.mp this).resolve_right ha
  exact ⟨h10, h20⟩

theorem p2_of_commute {w : SL(3, K)} {b c : K} (hb : b ≠ 0) (h : w * uSL 0 b c = uSL 0 b c * w) :
    (w : Matrix (Fin 3) (Fin 3) K) 2 0 = 0 ∧ (w : Matrix (Fin 3) (Fin 3) K) 2 1 = 0 := by
  set W := (w : Matrix (Fin 3) (Fin 3) K) with hW
  have e10 := entries_of_commute h 1 0
  have e11 := entries_of_commute h 1 1
  rw [(mul_u3Mat_apply W 0 b c 1).1, (u3Mat_mul_apply W 0 b c 0).2.1] at e10
  rw [(mul_u3Mat_apply W 0 b c 1).2.1, (u3Mat_mul_apply W 0 b c 1).2.1] at e11
  have h20 : W 2 0 = 0 := by
    have : b * W 2 0 = 0 := by linear_combination -e10
    exact (mul_eq_zero.mp this).resolve_left hb
  have h21 : W 2 1 = 0 := by
    have : b * W 2 1 = 0 := by linear_combination -e11
    exact (mul_eq_zero.mp this).resolve_left hb
  exact ⟨h20, h21⟩

theorem mem_heis_of_coe_eq {M : SL(3, K)} {a b c : K}
    (h : (M : Matrix (Fin 3) (Fin 3) K) = u3Mat a b c) : M ∈ heis K :=
  ⟨a, b, c, Subtype.ext h⟩

theorem eq_u3Mat_of_entries {M : Matrix (Fin 3) (Fin 3) K} (h00 : M 0 0 = 1) (h10 : M 1 0 = 0)
    (h20 : M 2 0 = 0) (h11 : M 1 1 = 1) (h21 : M 2 1 = 0) (h22 : M 2 2 = 1) :
    M = u3Mat (M 0 1) (M 1 2) (M 0 2) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [u3Mat, h00, h10, h20, h11, h21, h22]

theorem mem_heis_of_mul_eq_of_ut {M W R : SL(3, K)}
    (hW10 : (W : Matrix (Fin 3) (Fin 3) K) 1 0 = 0) (hW20 : (W : Matrix (Fin 3) (Fin 3) K) 2 0 = 0)
    (hW21 : (W : Matrix (Fin 3) (Fin 3) K) 2 1 = 0) (hR : R ∈ heis K) (h : M * W = W * R) :
    M ∈ heis K := by
  obtain ⟨a, b, c, rfl⟩ := hR
  have hm : (M : Matrix (Fin 3) (Fin 3) K) * (W : Matrix (Fin 3) (Fin 3) K) =
      (W : Matrix (Fin 3) (Fin 3) K) * u3Mat a b c := congrArg Subtype.val h
  set w := (W : Matrix (Fin 3) (Fin 3) K) with hw
  set m := (M : Matrix (Fin 3) (Fin 3) K) with hm'
  have hdet : w.det = 1 := W.2
  rw [Matrix.det_fin_three, hW10, hW20, hW21] at hdet
  have hd : w 0 0 * w 1 1 * w 2 2 = 1 := by linear_combination hdet
  have h0 : w 0 0 ≠ 0 := by intro h0; rw [h0] at hd; simp at hd
  have h1 : w 1 1 ≠ 0 := by intro h1; rw [h1] at hd; simp at hd
  have h2 : w 2 2 ≠ 0 := by intro h2; rw [h2] at hd; simp at hd
  have e : ∀ i j, m i 0 * w 0 j + m i 1 * w 1 j + m i 2 * w 2 j = (w * u3Mat a b c) i j :=
    fun i j => by rw [← mul_apply_three, hm]
  have e00 := e 0 0
  have e10 := e 1 0
  have e20 := e 2 0
  have e11 := e 1 1
  have e21 := e 2 1
  have e22 := e 2 2
  rw [(mul_u3Mat_apply w a b c 0).1] at e00
  rw [(mul_u3Mat_apply w a b c 1).1] at e10
  rw [(mul_u3Mat_apply w a b c 2).1] at e20
  rw [(mul_u3Mat_apply w a b c 1).2.1] at e11
  rw [(mul_u3Mat_apply w a b c 2).2.1] at e21
  rw [(mul_u3Mat_apply w a b c 2).2.2] at e22
  have m00 : m 0 0 = 1 := by
    have : (m 0 0 - 1) * w 0 0 = 0 := by
      linear_combination e00 - m 0 1 * hW10 - m 0 2 * hW20
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right h0)
  have m10 : m 1 0 = 0 := by
    have : m 1 0 * w 0 0 = 0 := by
      linear_combination e10 - m 1 1 * hW10 - m 1 2 * hW20 + hW10
    exact (mul_eq_zero.mp this).resolve_right h0
  have m20 : m 2 0 = 0 := by
    have : m 2 0 * w 0 0 = 0 := by
      linear_combination e20 - m 2 1 * hW10 - m 2 2 * hW20 + hW20
    exact (mul_eq_zero.mp this).resolve_right h0
  have m11 : m 1 1 = 1 := by
    have : (m 1 1 - 1) * w 1 1 = 0 := by
      linear_combination e11 - w 0 1 * m10 - m 1 2 * hW21 + a * hW10
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right h1)
  have m21 : m 2 1 = 0 := by
    have : m 2 1 * w 1 1 = 0 := by
      linear_combination e21 - w 0 1 * m20 - m 2 2 * hW21 + a * hW20 + hW21
    exact (mul_eq_zero.mp this).resolve_right h1
  have m22 : m 2 2 = 1 := by
    have : (m 2 2 - 1) * w 2 2 = 0 := by
      linear_combination e22 - w 0 2 * m20 - w 1 2 * m21 + c * hW20 + b * hW21
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right h2)
  exact mem_heis_of_coe_eq (eq_u3Mat_of_entries m00 m10 m20 m11 m21 m22)

theorem mem_heis_of_mul_eq_of_p1 {M W : SL(3, K)} {a c : K}
    (hW10 : (W : Matrix (Fin 3) (Fin 3) K) 1 0 = 0) (hW20 : (W : Matrix (Fin 3) (Fin 3) K) 2 0 = 0)
    (h : M * W = W * uSL a 0 c) : ∃ a' c' : K, M = uSL a' 0 c' := by
  have hm : (M : Matrix (Fin 3) (Fin 3) K) * (W : Matrix (Fin 3) (Fin 3) K) =
      (W : Matrix (Fin 3) (Fin 3) K) * u3Mat a 0 c := congrArg Subtype.val h
  set w := (W : Matrix (Fin 3) (Fin 3) K) with hw
  set m := (M : Matrix (Fin 3) (Fin 3) K) with hm'
  have hdet : w.det = 1 := W.2
  rw [Matrix.det_fin_three, hW10, hW20] at hdet
  have hd : w 0 0 * (w 1 1 * w 2 2 - w 1 2 * w 2 1) = 1 := by linear_combination hdet
  have h0 : w 0 0 ≠ 0 := left_ne_zero_of_mul_eq_one hd
  have hD : w 1 1 * w 2 2 - w 1 2 * w 2 1 ≠ 0 := right_ne_zero_of_mul_eq_one hd
  have e : ∀ i j, m i 0 * w 0 j + m i 1 * w 1 j + m i 2 * w 2 j = (w * u3Mat a 0 c) i j :=
    fun i j => by rw [← mul_apply_three, hm]
  have e00 := e 0 0
  have e10 := e 1 0
  have e20 := e 2 0
  have e11 := e 1 1
  have e12 := e 1 2
  have e21 := e 2 1
  have e22 := e 2 2
  rw [(mul_u3Mat_apply w a 0 c 0).1] at e00
  rw [(mul_u3Mat_apply w a 0 c 1).1] at e10
  rw [(mul_u3Mat_apply w a 0 c 2).1] at e20
  rw [(mul_u3Mat_apply w a 0 c 1).2.1] at e11
  rw [(mul_u3Mat_apply w a 0 c 1).2.2] at e12
  rw [(mul_u3Mat_apply w a 0 c 2).2.1] at e21
  rw [(mul_u3Mat_apply w a 0 c 2).2.2] at e22
  have m00 : m 0 0 = 1 := by
    have : (m 0 0 - 1) * w 0 0 = 0 := by
      linear_combination e00 - m 0 1 * hW10 - m 0 2 * hW20
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right h0)
  have m10 : m 1 0 = 0 := by
    have : m 1 0 * w 0 0 = 0 := by
      linear_combination e10 - m 1 1 * hW10 - m 1 2 * hW20 + hW10
    exact (mul_eq_zero.mp this).resolve_right h0
  have m20 : m 2 0 = 0 := by
    have : m 2 0 * w 0 0 = 0 := by
      linear_combination e20 - m 2 1 * hW10 - m 2 2 * hW20 + hW20
    exact (mul_eq_zero.mp this).resolve_right h0
  have f11 : (m 1 1 - 1) * w 1 1 + m 1 2 * w 2 1 = 0 := by
    linear_combination e11 - w 0 1 * m10 + a * hW10
  have f12 : (m 1 1 - 1) * w 1 2 + m 1 2 * w 2 2 = 0 := by
    linear_combination e12 - w 0 2 * m10 + c * hW10
  have f21 : m 2 1 * w 1 1 + (m 2 2 - 1) * w 2 1 = 0 := by
    linear_combination e21 - w 0 1 * m20 + a * hW20
  have f22 : m 2 1 * w 1 2 + (m 2 2 - 1) * w 2 2 = 0 := by
    linear_combination e22 - w 0 2 * m20 + c * hW20
  have m11 : m 1 1 = 1 := by
    have : (m 1 1 - 1) * (w 1 1 * w 2 2 - w 1 2 * w 2 1) = 0 := by
      linear_combination w 2 2 * f11 - w 2 1 * f12
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right hD)
  have m12 : m 1 2 = 0 := by
    have : m 1 2 * (w 1 1 * w 2 2 - w 1 2 * w 2 1) = 0 := by
      linear_combination w 1 1 * f12 - w 1 2 * f11
    exact (mul_eq_zero.mp this).resolve_right hD
  have m21 : m 2 1 = 0 := by
    have : m 2 1 * (w 1 1 * w 2 2 - w 1 2 * w 2 1) = 0 := by
      linear_combination w 2 2 * f21 - w 2 1 * f22
    exact (mul_eq_zero.mp this).resolve_right hD
  have m22 : m 2 2 = 1 := by
    have : (m 2 2 - 1) * (w 1 1 * w 2 2 - w 1 2 * w 2 1) = 0 := by
      linear_combination w 1 1 * f22 - w 1 2 * f21
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right hD)
  refine ⟨m 0 1, m 0 2, Subtype.ext ?_⟩
  change m = u3Mat (m 0 1) 0 (m 0 2)
  rw [← m12]
  exact eq_u3Mat_of_entries m00 m10 m20 m11 m21 m22

theorem mem_heis_of_mul_eq_of_p2 {M W : SL(3, K)} {b c : K}
    (hW20 : (W : Matrix (Fin 3) (Fin 3) K) 2 0 = 0) (hW21 : (W : Matrix (Fin 3) (Fin 3) K) 2 1 = 0)
    (h : M * W = W * uSL 0 b c) : ∃ b' c' : K, M = uSL 0 b' c' := by
  have hm : (M : Matrix (Fin 3) (Fin 3) K) * (W : Matrix (Fin 3) (Fin 3) K) =
      (W : Matrix (Fin 3) (Fin 3) K) * u3Mat 0 b c := congrArg Subtype.val h
  set w := (W : Matrix (Fin 3) (Fin 3) K) with hw
  set m := (M : Matrix (Fin 3) (Fin 3) K) with hm'
  have hdet : w.det = 1 := W.2
  rw [Matrix.det_fin_three, hW20, hW21] at hdet
  have hd : w 2 2 * (w 0 0 * w 1 1 - w 0 1 * w 1 0) = 1 := by linear_combination hdet
  have h2 : w 2 2 ≠ 0 := left_ne_zero_of_mul_eq_one hd
  have hD : w 0 0 * w 1 1 - w 0 1 * w 1 0 ≠ 0 := right_ne_zero_of_mul_eq_one hd
  have e : ∀ i j, m i 0 * w 0 j + m i 1 * w 1 j + m i 2 * w 2 j = (w * u3Mat 0 b c) i j :=
    fun i j => by rw [← mul_apply_three, hm]
  have e00 := e 0 0
  have e01 := e 0 1
  have e10 := e 1 0
  have e11 := e 1 1
  have e20 := e 2 0
  have e21 := e 2 1
  have e22 := e 2 2
  rw [(mul_u3Mat_apply w 0 b c 0).1] at e00
  rw [(mul_u3Mat_apply w 0 b c 0).2.1] at e01
  rw [(mul_u3Mat_apply w 0 b c 1).1] at e10
  rw [(mul_u3Mat_apply w 0 b c 1).2.1] at e11
  rw [(mul_u3Mat_apply w 0 b c 2).1] at e20
  rw [(mul_u3Mat_apply w 0 b c 2).2.1] at e21
  rw [(mul_u3Mat_apply w 0 b c 2).2.2] at e22
  have f20 : m 2 0 * w 0 0 + m 2 1 * w 1 0 = 0 := by
    linear_combination e20 - m 2 2 * hW20 + hW20
  have f21 : m 2 0 * w 0 1 + m 2 1 * w 1 1 = 0 := by
    linear_combination e21 - m 2 2 * hW21 + hW21
  have m20 : m 2 0 = 0 := by
    have : m 2 0 * (w 0 0 * w 1 1 - w 0 1 * w 1 0) = 0 := by
      linear_combination w 1 1 * f20 - w 1 0 * f21
    exact (mul_eq_zero.mp this).resolve_right hD
  have m21 : m 2 1 = 0 := by
    have : m 2 1 * (w 0 0 * w 1 1 - w 0 1 * w 1 0) = 0 := by
      linear_combination w 0 0 * f21 - w 0 1 * f20
    exact (mul_eq_zero.mp this).resolve_right hD
  have m22 : m 2 2 = 1 := by
    have : (m 2 2 - 1) * w 2 2 = 0 := by
      linear_combination e22 - w 0 2 * m20 - w 1 2 * m21 + c * hW20 + b * hW21
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right h2)
  have f00 : (m 0 0 - 1) * w 0 0 + m 0 1 * w 1 0 = 0 := by
    linear_combination e00 - m 0 2 * hW20
  have f01 : (m 0 0 - 1) * w 0 1 + m 0 1 * w 1 1 = 0 := by
    linear_combination e01 - m 0 2 * hW21
  have f10 : m 1 0 * w 0 0 + (m 1 1 - 1) * w 1 0 = 0 := by
    linear_combination e10 - m 1 2 * hW20
  have f11 : m 1 0 * w 0 1 + (m 1 1 - 1) * w 1 1 = 0 := by
    linear_combination e11 - m 1 2 * hW21
  have m00 : m 0 0 = 1 := by
    have : (m 0 0 - 1) * (w 0 0 * w 1 1 - w 0 1 * w 1 0) = 0 := by
      linear_combination w 1 1 * f00 - w 1 0 * f01
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right hD)
  have m01 : m 0 1 = 0 := by
    have : m 0 1 * (w 0 0 * w 1 1 - w 0 1 * w 1 0) = 0 := by
      linear_combination w 0 0 * f01 - w 0 1 * f00
    exact (mul_eq_zero.mp this).resolve_right hD
  have m10 : m 1 0 = 0 := by
    have : m 1 0 * (w 0 0 * w 1 1 - w 0 1 * w 1 0) = 0 := by
      linear_combination w 1 1 * f10 - w 1 0 * f11
    exact (mul_eq_zero.mp this).resolve_right hD
  have m11 : m 1 1 = 1 := by
    have : (m 1 1 - 1) * (w 0 0 * w 1 1 - w 0 1 * w 1 0) = 0 := by
      linear_combination w 0 0 * f11 - w 0 1 * f10
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right hD)
  refine ⟨m 1 2, m 0 2, Subtype.ext ?_⟩
  change m = u3Mat 0 (m 1 2) (m 0 2)
  rw [← m01]
  exact eq_u3Mat_of_entries m00 m10 m20 m11 m21 m22

theorem mem_heis_of_forall_commute [CharP K 3] {a₀ b₀ : K} (hab : a₀ ≠ 0 ∨ b₀ ≠ 0)
    {w : SL(3, K)} (hw : ∀ r ∈ lineSub a₀ b₀, w * r = r * w) : w ∈ heis K := by
  have hz := hw (uSL 0 0 1) ⟨0, 1, by rw [zero_mul, zero_mul]⟩
  obtain ⟨h10, h20, h21, h0022⟩ := ut_of_commute_z one_ne_zero hz
  have hx := hw (uSL a₀ b₀ 0) ⟨1, 0, by rw [one_mul, one_mul]⟩
  set W := (w : Matrix (Fin 3) (Fin 3) K) with hW
  have e01 := entries_of_commute hx 0 1
  have e12 := entries_of_commute hx 1 2
  rw [(mul_u3Mat_apply W a₀ b₀ 0 0).2.1, (u3Mat_mul_apply W a₀ b₀ 0 1).1] at e01
  rw [(mul_u3Mat_apply W a₀ b₀ 0 1).2.2, (u3Mat_mul_apply W a₀ b₀ 0 2).2.1] at e12
  have h11 : W 1 1 = W 0 0 := by
    rcases hab with ha | hb
    · have : a₀ * (W 0 0 - W 1 1) = 0 := by linear_combination e01 - 0 * h21
      exact (sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left ha)).symm
    · have : b₀ * (W 1 1 - W 2 2) = 0 := by linear_combination e12 - 0 * h10
      rw [h0022]
      exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left hb)
  have hdet : W.det = 1 := w.2
  rw [Matrix.det_fin_three, h10, h20, h21, h11, ← h0022] at hdet
  have h00 : W 0 0 = 1 := eq_one_of_pow_three_eq_one (by linear_combination hdet)
  exact mem_heis_of_coe_eq (eq_u3Mat_of_entries h00 h10 h20 (h11.trans h00) h21
    (h0022.symm.trans h00))

end Centralizers

section Normalized

variable {K : Type} [Field K]

theorem pow_three_eq_one_of_mem_heis [CharP K 3] {g : SL(3, K)} (hg : g ∈ heis K) : g ^ 3 = 1 := by
  obtain ⟨a, b, c, rfl⟩ := hg
  exact uSL_pow_three a b c

theorem commutator_mem_heis {a₀ b₀ : K} {v w r : SL(3, K)} (hv : v ∈ lineSub a₀ b₀) (hv1 : v ≠ 1)
    (hwv : w * v = v * w) (hr : r ∈ lineSub a₀ b₀) : r * w * r⁻¹ * w⁻¹ ∈ heis K := by
  obtain ⟨s, c, rfl⟩ := hv
  have hrU : r⁻¹ ∈ heis K := (heis K).inv_mem (lineSub_le_heis a₀ b₀ hr)
  have hM : (w * r⁻¹ * w⁻¹) * w = w * r⁻¹ := by group
  have hfin : ∀ M : SL(3, K), M = w * r⁻¹ * w⁻¹ → M ∈ heis K → r * w * r⁻¹ * w⁻¹ ∈ heis K := by
    rintro M rfl hM'
    have : r * w * r⁻¹ * w⁻¹ = r * (w * r⁻¹ * w⁻¹) := by group
    rw [this]
    exact (heis K).mul_mem (lineSub_le_heis a₀ b₀ hr) hM'
  by_cases ha : s * a₀ = 0 <;> by_cases hb : s * b₀ = 0
  ·
    rw [ha, hb] at hwv hv1
    have hc : c ≠ 0 := by
      rintro rfl
      exact hv1 uSL_zero
    obtain ⟨h10, h20, h21, -⟩ := ut_of_commute_z hc hwv
    exact hfin _ rfl (mem_heis_of_mul_eq_of_ut h10 h20 h21 hrU hM)
  ·
    rw [ha] at hwv
    obtain ⟨h20, h21⟩ := p2_of_commute hb hwv
    have hs : s ≠ 0 := fun h0 => hb (by rw [h0, zero_mul])
    have ha₀ : a₀ = 0 := (mul_eq_zero.mp ha).resolve_left hs
    obtain ⟨t, d, rfl⟩ := hr
    have hrinv : (uSL (t * a₀) (t * b₀) d)⁻¹ = uSL 0 (-(t * b₀)) (-d) := by
      rw [uSL_inv, ha₀]
      congr 1 <;> ring
    have hM2 : (w * (uSL (t * a₀) (t * b₀) d)⁻¹ * w⁻¹) * w = w * uSL 0 (-(t * b₀)) (-d) := by
      rw [hM, hrinv]
    obtain ⟨b', c', hM'⟩ := mem_heis_of_mul_eq_of_p2 h20 h21 hM2
    exact hfin _ rfl (by rw [hM']; exact ⟨0, b', c', rfl⟩)
  ·
    rw [hb] at hwv
    obtain ⟨h10, h20⟩ := p1_of_commute ha hwv
    have hs : s ≠ 0 := fun h0 => ha (by rw [h0, zero_mul])
    have hb₀ : b₀ = 0 := (mul_eq_zero.mp hb).resolve_left hs
    obtain ⟨t, d, rfl⟩ := hr
    have hrinv : (uSL (t * a₀) (t * b₀) d)⁻¹ = uSL (-(t * a₀)) 0 (-d) := by
      rw [uSL_inv, hb₀]
      congr 1 <;> ring
    have hM2 : (w * (uSL (t * a₀) (t * b₀) d)⁻¹ * w⁻¹) * w = w * uSL (-(t * a₀)) 0 (-d) := by
      rw [hM, hrinv]
    obtain ⟨a', c', hM'⟩ := mem_heis_of_mul_eq_of_p1 h10 h20 hM2
    exact hfin _ rfl (by rw [hM']; exact ⟨a', 0, c', rfl⟩)
  ·
    obtain ⟨h10, h20, h21⟩ := ut_of_commute_regular ha hb hwv
    exact hfin _ rfl (mem_heis_of_mul_eq_of_ut h10 h20 h21 hrU hM)

theorem eq_bot_of_le_normalizer_lineSub [CharP K 3] [Finite K] {a₀ b₀ : K}
    (hab : a₀ ≠ 0 ∨ b₀ ≠ 0) {W : Subgroup SL(3, K)} (hW3 : ¬ 3 ∣ Nat.card W)
    (hRW : lineSub a₀ b₀ ≤ Subgroup.normalizer (W : Set SL(3, K))) : W = ⊥ := by
  have : Finite SL(3, K) := Finite.of_injective _ Subtype.val_injective
  have hcop : Nat.Coprime 3 (Nat.card W) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hW3
  have hW1 : ∀ w ∈ W, w ^ 3 = 1 → w = 1 := by
    intro w hw hw3
    have hd1 : orderOf (⟨w, hw⟩ : W) ∣ 3 := by
      rw [orderOf_dvd_iff_pow_eq_one]
      exact Subtype.ext (by rw [Subgroup.coe_pow, hw3, Subgroup.coe_one])
    have h1 : orderOf (⟨w, hw⟩ : W) = 1 :=
      Nat.eq_one_of_dvd_coprimes hcop hd1 (orderOf_dvd_natCard _)
    exact congrArg Subtype.val (orderOf_eq_one_iff.mp h1)
  have hK3 : 3 ≤ Nat.card K := by
    have : Fintype K := Fintype.ofFinite K
    obtain ⟨n, -, hn⟩ := FiniteField.card K 3
    rw [Nat.card_eq_fintype_card, hn]
    calc 3 = 3 ^ 1 := by norm_num
      _ ≤ 3 ^ (n : ℕ) := Nat.pow_le_pow_right (by norm_num) n.pos
  rw [eq_bot_iff]
  refine Sec5.le_of_forall_inf_centralizer_le Nat.prime_three (isElemAbelian_lineSub a₀ b₀)
    (by rw [card_lineSub hab]; exact Nat.pow_le_pow_left hK3 2) hRW hcop fun v hvR hv1 => ?_
  rintro w ⟨hwW, hwv⟩
  have hwv' : w * v = v * w := Subgroup.mem_centralizer_singleton_iff.mp hwv
  have hcomm : ∀ r ∈ lineSub a₀ b₀, w * r = r * w := by
    intro r hr
    have hU := commutator_mem_heis hvR hv1 hwv' hr
    have hW' : r * w * r⁻¹ * w⁻¹ ∈ W :=
      W.mul_mem ((Subgroup.mem_normalizer_iff.mp (hRW hr) w).mp hwW) (W.inv_mem hwW)
    have h1 := hW1 _ hW' (pow_three_eq_one_of_mem_heis hU)
    have key : w * r = (r * w * r⁻¹ * w⁻¹)⁻¹ * (r * w) := by group
    rw [key, h1, inv_one, one_mul]
  exact Subgroup.mem_bot.mpr (hW1 w hwW (pow_three_eq_one_of_mem_heis
    (mem_heis_of_forall_commute hab hcomm)))

end Normalized

section Three

theorem false_of_dual_fix {K : Type} [Field K] (h2 : (2 : K) ≠ 0) {A : Matrix (Fin 3) (Fin 3) K}
    (hA : A.det ≠ 0) {a b c : K} (hab : a ≠ 0 ∨ b ≠ 0)
    (hz : A * (u3Mat 0 0 (-1))ᵀ = u3Mat 0 0 1 * A)
    (hx : A * (u3Mat (-a) (-b) (a * b - c))ᵀ = u3Mat a b c * A) : False := by
  have z00 := congrFun (congrFun hz 0) 0
  have z01 := congrFun (congrFun hz 0) 1
  have z02 := congrFun (congrFun hz 0) 2
  have z10 := congrFun (congrFun hz 1) 0
  simp [Matrix.mul_apply, Fin.sum_univ_three, u3Mat] at z00 z01 z02 z10
  have x10 := congrFun (congrFun hx 1) 0
  have x01 := congrFun (congrFun hx 0) 1
  simp [Matrix.mul_apply, Fin.sum_univ_three, u3Mat] at x10 x01
  have h21 : A 2 1 = 0 := z01
  have h22 : A 2 2 = 0 := z02
  have h12 : A 1 2 = 0 := z10
  have h20 : A 2 0 = -A 0 2 := by linear_combination -z00
  have hdet : A.det = A 0 2 ^ 2 * A 1 1 := by
    rw [Matrix.det_fin_three, h21, h22, h12, h20]
    ring
  rw [hdet] at hA
  have hβ : A 0 2 ≠ 0 := fun h => hA (by rw [h]; ring)
  have hs : A 1 1 ≠ 0 := fun h => hA (by rw [h]; ring)
  have e1 : a * A 1 1 = b * A 0 2 := by linear_combination -x10 + (a * b - c) * h12 - b * h20
  have e2 : a * A 1 1 = -(b * A 0 2) := by linear_combination -x01 - c * h21
  have hb : b = 0 := by
    have : 2 * (b * A 0 2) = 0 := by linear_combination e2 - e1
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h h2
    · exact (mul_eq_zero.mp h).resolve_right hβ
  have ha : a = 0 := by
    rw [hb, zero_mul] at e1
    exact (mul_eq_zero.mp e1).resolve_right hs
  rcases hab with h | h
  · exact h ha
  · exact h hb

theorem ringAut_galois_three_eq_one (σ : GaloisField 3 1 ≃+* GaloisField 3 1) : σ = 1 := by
  have hcard := (CFSG.LocalAnalysis.ComponentInitial.card_ringAut_and_isCyclic Nat.prime_three
    (GaloisField 3 1) (GaloisField.card 3 1 one_ne_zero)).1
  have : Subsingleton (RingAut (GaloisField 3 1)) := (Nat.card_eq_one_iff_unique.mp hcard).1
  exact Subsingleton.elim _ _

theorem sq_eq_one_galois_three (d : (GaloisField 3 1)ˣ) : (d : GaloisField 3 1) ^ 2 = 1 := by
  have : Fintype (GaloisField 3 1) := Fintype.ofFinite _
  have hcard : Fintype.card (GaloisField 3 1) = 3 := by
    rw [← Nat.card_eq_fintype_card, GaloisField.card 3 1 one_ne_zero, pow_one]
  have h := FiniteField.pow_card (d : GaloisField 3 1)
  rw [hcard] at h
  have hd : (d : GaloisField 3 1) ≠ 0 := d.ne_zero
  have : (d : GaloisField 3 1) * ((d : GaloisField 3 1) ^ 2 - 1) = 0 := by
    linear_combination h
  exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left hd)

theorem mem_inner_of_fix_three {y : MulAut SL(3, GaloisField 3 1)} {a b c : GaloisField 3 1}
    (hab : a ≠ 0 ∨ b ≠ 0) (hz : y (uSL 0 0 1) = uSL 0 0 1) (hx : y (uSL a b c) = uSL a b c) :
    y ∈ inner SL(3, GaloisField 3 1) := by
  have h2 : (2 : GaloisField 3 1) ≠ 0 := by
    intro h
    have h' : ((2 : ℕ) : GaloisField 3 1) = 0 := by exact_mod_cast h
    rw [CharP.cast_eq_zero_iff (GaloisField 3 1) 3] at h'
    norm_num at h'
  have hι : ∀ g, slEquivProjectiveSL (GaloisField 3 1) g =
      CFSG.LocalAnalysis.ComponentInitial.LinearFlag.proj 3 (GaloisField 3 1) g := fun g => rfl
  have hproj : Function.Injective
      (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.proj 3 (GaloisField 3 1)) := by
    intro g g' h
    apply (slEquivProjectiveSL (GaloisField 3 1)).injective
    rw [hι, hι, h]
  set α := MulAut.congr (slEquivProjectiveSL (GaloisField 3 1)) y with hαdef
  have hα : ∀ g, α (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.proj 3 (GaloisField 3 1) g) =
      CFSG.LocalAnalysis.ComponentInitial.LinearFlag.proj 3 (GaloisField 3 1) (y g) := by
    intro g
    rw [← hι, ← hι]
    change slEquivProjectiveSL (GaloisField 3 1) (y ((slEquivProjectiveSL (GaloisField 3 1)).symm
      (slEquivProjectiveSL (GaloisField 3 1) g))) = _
    rw [MulEquiv.symm_apply_apply]
  obtain ⟨A, σ, ε, hε, hAσ⟩ :=
    (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.automorphism_generation
      (K := GaloisField 3 1) (n := 3) le_rfl).2 α
  rw [ringAut_galois_three_eq_one σ, map_one, mul_one] at hAσ
  have hAdet : (A : Matrix (Fin 3) (Fin 3) (GaloisField 3 1)).det ≠ 0 := by
    rw [← GeneralLinearGroup.val_det_apply]
    exact (GeneralLinearGroup.det A).ne_zero
  have hAinv : ((A⁻¹ : GL (Fin 3) (GaloisField 3 1)) : Matrix (Fin 3) (Fin 3) (GaloisField 3 1)) *
      (A : Matrix (Fin 3) (Fin 3) (GaloisField 3 1)) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  rcases (show ε = 0 ∨ ε = 1 by omega) with rfl | rfl
  ·
    rw [pow_zero, mul_one] at hAσ
    have hy : ∀ g, y g =
        CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 3
          (GaloisField 3 1) A g := by
      intro g
      apply hproj
      rw [← hα, hAσ, CFSG.LocalAnalysis.ComponentInitial.LinearFlag.conjAut_proj]
    set d := GeneralLinearGroup.det A with hd
    have hd2 := sq_eq_one_galois_three d
    have hdet' : ((d : GaloisField 3 1) • (A : Matrix (Fin 3) (Fin 3) (GaloisField 3 1))).det =
        1 := by
      rw [Matrix.det_smul, Fintype.card_fin, hd, GeneralLinearGroup.val_det_apply]
      have : ((A : Matrix (Fin 3) (Fin 3) (GaloisField 3 1)).det) ^ 2 = 1 := by
        rw [← GeneralLinearGroup.val_det_apply]
        exact hd2
      linear_combination ((A : Matrix (Fin 3) (Fin 3) (GaloisField 3 1)).det ^ 2 + 1) * this
    set g' : SL(3, GaloisField 3 1) := ⟨(d : GaloisField 3 1) •
      (A : Matrix (Fin 3) (Fin 3) (GaloisField 3 1)), hdet'⟩ with hg'
    refine ⟨g', MulEquiv.ext fun g => ?_⟩
    rw [MulAut.conj_apply, hy]
    symm
    rw [eq_mul_inv_iff_mul_eq]
    apply Subtype.ext
    change ((CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 3
        (GaloisField 3 1) A g : SL(3, GaloisField 3 1)) :
          Matrix (Fin 3) (Fin 3) (GaloisField 3 1)) *
        ((d : GaloisField 3 1) • (A : Matrix (Fin 3) (Fin 3) (GaloisField 3 1))) =
      ((d : GaloisField 3 1) • (A : Matrix (Fin 3) (Fin 3) (GaloisField 3 1))) *
        (g : Matrix (Fin 3) (Fin 3) (GaloisField 3 1))
    rw [CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation_matrix,
      Matrix.mul_smul, Matrix.smul_mul]
    congr 1
    simp only [Matrix.mul_assoc, hAinv, Matrix.mul_one]
  ·
    exfalso
    rw [pow_one] at hAσ
    have hy : ∀ g, y g =
        CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 3
          (GaloisField 3 1) A (g⁻¹).transpose := by
      intro g
      apply hproj
      rw [← hα, hAσ, MulAut.mul_apply,
        CFSG.LocalAnalysis.ComponentInitial.LinearFlag.dualAut_proj,
        CFSG.LocalAnalysis.ComponentInitial.LinearFlag.conjAut_proj]
    have hmat : ∀ g : SL(3, GaloisField 3 1), y g = g →
        (A : Matrix (Fin 3) (Fin 3) (GaloisField 3 1)) *
          (((g⁻¹ : SL(3, GaloisField 3 1)) : Matrix (Fin 3) (Fin 3) (GaloisField 3 1)))ᵀ =
        (g : Matrix (Fin 3) (Fin 3) (GaloisField 3 1)) *
          (A : Matrix (Fin 3) (Fin 3) (GaloisField 3 1)) := by
      intro g hg
      have h1 := congrArg (fun k : SL(3, GaloisField 3 1) =>
        (k : Matrix (Fin 3) (Fin 3) (GaloisField 3 1))) ((hy g).symm.trans hg)
      simp only [CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation_matrix,
        SpecialLinearGroup.coe_transpose] at h1
      rw [← h1, Matrix.mul_assoc, Matrix.mul_assoc, hAinv, Matrix.mul_one]
    have hz' := hmat _ hz
    have hx' := hmat _ hx
    rw [uSL_inv, coe_uSL, coe_uSL] at hz' hx'
    simp only [neg_zero, mul_zero, zero_sub] at hz'
    exact false_of_dual_fix h2 hAdet hab hz' hx'

end Three

section KillThree

theorem mulAut_mul_conj_mul_inv {X : Type*} [Group X] (φ : MulAut X) (x : X) :
    φ * MulAut.conj x * φ⁻¹ = MulAut.conj (φ x) := by
  ext y
  change φ (x * φ.symm y * x⁻¹) = φ x * y * (φ x)⁻¹
  rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]

theorem eq_bot_of_le_normalizer_three {a₀ b₀ : GaloisField 3 1} (hab : a₀ ≠ 0 ∨ b₀ ≠ 0)
    {Y : Subgroup (MulAut SL(3, GaloisField 3 1))} (hY3 : ¬ 3 ∣ Nat.card Y)
    (hRY : (lineSub a₀ b₀).map (MulAut.conj : SL(3, GaloisField 3 1) →* _) ≤
      Subgroup.normalizer (Y : Set (MulAut SL(3, GaloisField 3 1)))) : Y = ⊥ := by
  set I := inner SL(3, GaloisField 3 1) with hI
  have hinj := Item434Kit.conj_injective_of_center_eq_bot (center_SL_three_eq_bot (GaloisField 3 1))
  set W : Subgroup SL(3, GaloisField 3 1) := (Y ⊓ I).comap MulAut.conj with hW
  have hWmap : W.map MulAut.conj = Y ⊓ I := Subgroup.map_comap_eq_self inf_le_right
  have hWcard : Nat.card W = Nat.card (Y ⊓ I : Subgroup _) := by
    rw [← hWmap, Subgroup.card_map_of_injective hinj]
  have hW3 : ¬ 3 ∣ Nat.card W := by
    rw [hWcard]
    exact fun h3 => hY3 (h3.trans (Subgroup.card_dvd_of_le inf_le_left))
  have hconjR : ∀ r ∈ lineSub a₀ b₀, ∀ w ∈ W, r * w * r⁻¹ ∈ W := by
    intro r hr w hw
    have hY : MulAut.conj r * MulAut.conj w * (MulAut.conj r)⁻¹ ∈ Y :=
      (Subgroup.mem_normalizer_iff.mp (hRY ⟨r, hr, rfl⟩) _).mp hw.1
    change MulAut.conj (r * w * r⁻¹) ∈ Y ⊓ I
    rw [map_mul, map_mul, map_inv]
    exact ⟨hY, ⟨r * w * r⁻¹, by rw [map_mul, map_mul, map_inv]⟩⟩
  have hRW : lineSub a₀ b₀ ≤ Subgroup.normalizer (W : Set SL(3, GaloisField 3 1)) := by
    intro r hr
    rw [Subgroup.mem_normalizer_iff]
    intro w
    refine ⟨hconjR r hr w, fun hw => ?_⟩
    have h1 := hconjR r⁻¹ ((lineSub a₀ b₀).inv_mem hr) _ hw
    rwa [show r⁻¹ * (r * w * r⁻¹) * r⁻¹⁻¹ = w by group] at h1
  have hWbot := eq_bot_of_le_normalizer_lineSub hab hW3 hRW
  have hYI : Y ⊓ I = ⊥ := by rw [← hWmap, hWbot, Subgroup.map_bot]
  rw [eq_bot_iff]
  intro y hy
  have hfix : ∀ r ∈ lineSub a₀ b₀, y r = r := by
    intro r hr
    have hcR := hRY ⟨r, hr, rfl⟩
    have hmemY : MulAut.conj r * y * (MulAut.conj r)⁻¹ * y⁻¹ ∈ Y :=
      Y.mul_mem ((Subgroup.mem_normalizer_iff.mp hcR y).mp hy) (Y.inv_mem hy)
    have hmemI : MulAut.conj r * y * (MulAut.conj r)⁻¹ * y⁻¹ ∈ I := by
      have e : MulAut.conj r * y * (MulAut.conj r)⁻¹ * y⁻¹ =
          MulAut.conj r * (y * MulAut.conj r⁻¹ * y⁻¹) := by rw [map_inv]; group
      rw [e, mulAut_mul_conj_mul_inv]
      exact I.mul_mem ⟨r, rfl⟩ ⟨y r⁻¹, rfl⟩
    have h1 : MulAut.conj r * y * (MulAut.conj r)⁻¹ * y⁻¹ = 1 := by
      have hmem : MulAut.conj r * y * (MulAut.conj r)⁻¹ * y⁻¹ ∈ Y ⊓ I := ⟨hmemY, hmemI⟩
      rwa [hYI, Subgroup.mem_bot] at hmem
    have h2 : y * MulAut.conj r * y⁻¹ = MulAut.conj r := by
      have e : y * MulAut.conj r * y⁻¹ =
          (MulAut.conj r * y * (MulAut.conj r)⁻¹ * y⁻¹)⁻¹ * MulAut.conj r := by group
      rw [e, h1, inv_one, one_mul]
    rw [mulAut_mul_conj_mul_inv] at h2
    exact hinj h2
  have hyI : y ∈ I := mem_inner_of_fix_three (c := 0) hab
    (hfix _ ⟨0, 1, by rw [zero_mul, zero_mul]⟩) (hfix _ ⟨1, 0, by rw [one_mul, one_mul]⟩)
  have hmem : y ∈ Y ⊓ I := ⟨hy, hyI⟩
  rwa [hYI] at hmem

end KillThree

end CFSG.RankThree.PartTwo.Sec4.Item434CharThree
