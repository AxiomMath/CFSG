module

public import CFSG.RankThree.GF2n.Stroth80.Sec715TriOct
public import Mathlib.Algebra.CharP.Two

public section

namespace CFSG.RankThree.GF2n.Stroth80.Tri

open CFSG.Open

variable {K : Type*} [CommRing K]

@[simp] theorem octA_octMk (a : K) (u w : Fin 3 → K) (b : K) : octA (octMk a u w b) = a := rfl

@[simp] theorem octB_octMk (a : K) (u w : Fin 3 → K) (b : K) : octB (octMk a u w b) = b := rfl

@[simp] theorem octU_octMk (a : K) (u w : Fin 3 → K) (b : K) (i : Fin 3) :
    octU (octMk a u w b) i = u i := rfl

@[simp] theorem octW_octMk (a : K) (u w : Fin 3 → K) (b : K) (i : Fin 3) :
    octW (octMk a u w b) i = w i := rfl

@[simp] theorem octMk_octA (x : Oct K) : octMk (octA x) (octU x) (octW x) (octB x) = x := by
  funext i
  rcases i with i | i
  · induction i using Fin.cases <;> rfl
  · induction i using Fin.cases <;> rfl

theorem oct_ext {x y : Oct K} (hA : octA x = octA y) (hU : octU x = octU y)
    (hW : octW x = octW y) (hB : octB x = octB y) : x = y := by
  funext i
  rcases i with i | i
  · induction i using Fin.cases with
    | zero => exact hA
    | succ j => exact congrFun hU j
  · induction i using Fin.cases with
    | zero => exact hB
    | succ j => exact congrFun hW j

theorem oct_ext_coords {x y : Oct K} (hA : octA x = octA y) (hB : octB x = octB y)
    (hU₀ : octU x 0 = octU y 0) (hU₁ : octU x 1 = octU y 1) (hU₂ : octU x 2 = octU y 2)
    (hW₀ : octW x 0 = octW y 0) (hW₁ : octW x 1 = octW y 1) (hW₂ : octW x 2 = octW y 2) :
    x = y :=
  oct_ext hA (funext fun i => by fin_cases i <;> assumption)
    (funext fun i => by fin_cases i <;> assumption) hB

theorem cross3_apply_zero (u w : Fin 3 → K) : cross3 u w 0 = u 1 * w 2 - u 2 * w 1 := rfl

theorem cross3_apply_one (u w : Fin 3 → K) : cross3 u w 1 = u 2 * w 0 - u 0 * w 2 := rfl

theorem cross3_apply_two (u w : Fin 3 → K) : cross3 u w 2 = u 0 * w 1 - u 1 * w 0 := rfl

@[simp] theorem octA_add (x y : Oct K) : octA (x + y) = octA x + octA y := rfl

@[simp] theorem octB_add (x y : Oct K) : octB (x + y) = octB x + octB y := rfl

@[simp] theorem octU_add (x y : Oct K) (i : Fin 3) : octU (x + y) i = octU x i + octU y i := rfl

@[simp] theorem octW_add (x y : Oct K) (i : Fin 3) : octW (x + y) i = octW x i + octW y i := rfl

@[simp] theorem octA_smul (c : K) (x : Oct K) : octA (c • x) = c * octA x := rfl

@[simp] theorem octB_smul (c : K) (x : Oct K) : octB (c • x) = c * octB x := rfl

@[simp] theorem octU_smul (c : K) (x : Oct K) (i : Fin 3) : octU (c • x) i = c * octU x i := rfl

@[simp] theorem octW_smul (c : K) (x : Oct K) (i : Fin 3) : octW (c • x) i = c * octW x i := rfl

@[simp] theorem octA_neg (x : Oct K) : octA (-x) = -octA x := rfl

@[simp] theorem octB_neg (x : Oct K) : octB (-x) = -octB x := rfl

@[simp] theorem octU_neg (x : Oct K) (i : Fin 3) : octU (-x) i = -octU x i := rfl

@[simp] theorem octW_neg (x : Oct K) (i : Fin 3) : octW (-x) i = -octW x i := rfl

@[simp] theorem octA_zero : octA (0 : Oct K) = 0 := rfl

@[simp] theorem octB_zero : octB (0 : Oct K) = 0 := rfl

@[simp] theorem octU_zero (i : Fin 3) : octU (0 : Oct K) i = 0 := rfl

@[simp] theorem octW_zero (i : Fin 3) : octW (0 : Oct K) i = 0 := rfl

@[simp] theorem octA_octMul (x y : Oct K) :
    octA (octMul x y) = octA x * octA y + dot3 (octU x) (octW y) := rfl

@[simp] theorem octB_octMul (x y : Oct K) :
    octB (octMul x y) = octB x * octB y + dot3 (octW x) (octU y) := rfl

@[simp] theorem octU_octMul (x y : Oct K) (i : Fin 3) :
    octU (octMul x y) i = octA x * octU y i + octB y * octU x i - cross3 (octW x) (octW y) i :=
  rfl

@[simp] theorem octW_octMul (x y : Oct K) (i : Fin 3) :
    octW (octMul x y) i = octA y * octW x i + octB x * octW y i + cross3 (octU x) (octU y) i :=
  rfl

@[simp] theorem octA_octConj (x : Oct K) : octA (octConj x) = octB x := rfl

@[simp] theorem octB_octConj (x : Oct K) : octB (octConj x) = octA x := rfl

@[simp] theorem octU_octConj (x : Oct K) (i : Fin 3) : octU (octConj x) i = -octU x i := rfl

@[simp] theorem octW_octConj (x : Oct K) (i : Fin 3) : octW (octConj x) i = -octW x i := rfl

@[simp] theorem octA_octOne : octA (octOne : Oct K) = 1 := rfl

@[simp] theorem octB_octOne : octB (octOne : Oct K) = 1 := rfl

@[simp] theorem octU_octOne (i : Fin 3) : octU (octOne : Oct K) i = 0 := rfl

@[simp] theorem octW_octOne (i : Fin 3) : octW (octOne : Oct K) i = 0 := rfl

@[expose] def octTr (x : Oct K) : K := octA x + octB x

@[expose] def octPolar (x y : Oct K) : K := octNorm (x + y) - octNorm x - octNorm y

local syntax (name := octExpand) "oct_expand" : tactic

local macro_rules
  | `(tactic| oct_expand) =>
    `(tactic| simp only [octA_add, octB_add, octU_add, octW_add, octA_smul, octB_smul, octU_smul,
      octW_smul, octA_neg, octB_neg, octU_neg, octW_neg, octA_zero, octB_zero, octU_zero,
      octW_zero, octA_octMul, octB_octMul, octU_octMul, octW_octMul, octA_octConj, octB_octConj,
      octU_octConj, octW_octConj, octA_octOne, octB_octOne, octU_octOne, octW_octOne, dot3,
      cross3_apply_zero, cross3_apply_one, cross3_apply_two, octNorm, octTr, octPolar])

local syntax (name := octRing) "oct_ring" : tactic

local macro_rules
  | `(tactic| oct_ring) =>
    `(tactic| (refine oct_ext_coords ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> oct_expand <;> ring))

theorem octMul_add_left (x x' y : Oct K) : octMul (x + x') y = octMul x y + octMul x' y := by
  oct_ring

theorem octMul_add_right (x y y' : Oct K) : octMul x (y + y') = octMul x y + octMul x y' := by
  oct_ring

theorem octMul_smul_left (c : K) (x y : Oct K) : octMul (c • x) y = c • octMul x y := by
  oct_ring

theorem octMul_smul_right (c : K) (x y : Oct K) : octMul x (c • y) = c • octMul x y := by
  oct_ring

@[simp] theorem octMul_zero_left (y : Oct K) : octMul 0 y = 0 := by oct_ring

@[simp] theorem octMul_zero_right (x : Oct K) : octMul x 0 = 0 := by oct_ring

theorem octMul_neg_right (x y : Oct K) : octMul x (-y) = -octMul x y := by oct_ring

theorem octMul_sub_right (x y y' : Oct K) : octMul x (y - y') = octMul x y - octMul x y' := by
  rw [sub_eq_add_neg, octMul_add_right, octMul_neg_right, ← sub_eq_add_neg]

@[expose] def octMulBil : Oct K →ₗ[K] Oct K →ₗ[K] Oct K :=
  LinearMap.mk₂ K octMul octMul_add_left octMul_smul_left octMul_add_right octMul_smul_right

@[simp] theorem octMulBil_apply (x y : Oct K) : octMulBil x y = octMul x y := rfl

@[simp] theorem octMul_one (x : Oct K) : octMul x octOne = x := by oct_ring

@[simp] theorem octOne_mul (x : Oct K) : octMul octOne x = x := by oct_ring

@[simp] theorem octNorm_one : octNorm (octOne : Oct K) = 1 := by oct_expand; ring

theorem octNorm_mul (x y : Oct K) : octNorm (octMul x y) = octNorm x * octNorm y := by
  oct_expand; ring

@[simp] theorem octConj_conj (x : Oct K) : octConj (octConj x) = x := by oct_ring

@[simp] theorem octNorm_conj (x : Oct K) : octNorm (octConj x) = octNorm x := by
  oct_expand; ring

theorem octConj_mul (x y : Oct K) : octConj (octMul x y) = octMul (octConj y) (octConj x) := by
  oct_ring

theorem octMul_conj_mul (x y : Oct K) : octMul (octConj x) (octMul x y) = octNorm x • y := by
  oct_ring

theorem octMul_mul_conj_left (x y : Oct K) :
    octMul x (octMul (octConj x) y) = octNorm x • y := by
  oct_ring

theorem octMul_mul_conj (x y : Oct K) : octMul (octMul y x) (octConj x) = octNorm x • y := by
  oct_ring

theorem octMul_mul_conj_right (x y : Oct K) :
    octMul (octMul y (octConj x)) x = octNorm x • y := by
  oct_ring

theorem octPolar_eq (x y : Oct K) :
    octPolar x y = octA x * octB y + octA y * octB x - dot3 (octU x) (octW y)
      - dot3 (octU y) (octW x) := by
  oct_expand; ring

theorem octPolar_comm (x y : Oct K) : octPolar x y = octPolar y x := by oct_expand; ring

theorem octPolar_add_left (x x' y : Oct K) :
    octPolar (x + x') y = octPolar x y + octPolar x' y := by
  oct_expand; ring

theorem octPolar_add_right (x y y' : Oct K) :
    octPolar x (y + y') = octPolar x y + octPolar x y' := by
  oct_expand; ring

theorem octPolar_smul_left (c : K) (x y : Oct K) : octPolar (c • x) y = c * octPolar x y := by
  oct_expand; ring

theorem octPolar_smul_right (c : K) (x y : Oct K) : octPolar x (c • y) = c * octPolar x y := by
  oct_expand; ring

@[expose] def octPolarBil : Oct K →ₗ[K] Oct K →ₗ[K] K :=
  LinearMap.mk₂ K octPolar octPolar_add_left octPolar_smul_left octPolar_add_right
    octPolar_smul_right

@[simp] theorem octPolarBil_apply (x y : Oct K) : octPolarBil x y = octPolar x y := rfl

theorem octMul_conj_mul_lin (x x' y : Oct K) :
    octMul (octConj x) (octMul x' y) + octMul (octConj x') (octMul x y) = octPolar x x' • y := by
  oct_ring

theorem octMul_mul_conj_lin (x x' y : Oct K) :
    octMul (octMul y x) (octConj x') + octMul (octMul y x') (octConj x) = octPolar x x' • y := by
  oct_ring

theorem octPolar_mul_left (x y z : Oct K) :
    octPolar (octMul x y) (octMul x z) = octNorm x * octPolar y z := by
  unfold octPolar
  rw [← octMul_add_right, octNorm_mul, octNorm_mul, octNorm_mul]
  ring

theorem octPolar_mul_right (x y z : Oct K) :
    octPolar (octMul y x) (octMul z x) = octNorm x * octPolar y z := by
  unfold octPolar
  rw [← octMul_add_left, octNorm_mul, octNorm_mul, octNorm_mul]
  ring

section CharTwo

variable [CharP K 2]

theorem octPolar_eq_char2 (x y : Oct K) :
    octPolar x y = ∑ i : Fin 4, (x (.inl i) * y (.inr i) + y (.inl i) * x (.inr i)) := by
  rw [octPolar_eq, Fin.sum_univ_succ]
  simp only [Fin.sum_univ_three, dot3, octA, octB, octU, octW, CharTwo.sub_eq_add]
  ring

end CharTwo

theorem octNorm_eq_statedQuadPlus {K : Type} [Field K] [CharP K 2] (x : Oct K) :
    octNorm x = StatedQuadPlus 4 K x := by
  simp only [StatedQuadPlus, CFSG.MatrixModel.plusQuadCore]
  rw [Fin.sum_univ_succ]
  simp only [octNorm, Fin.sum_univ_three, dot3, octA, octB, octU, octW, CharTwo.sub_eq_add]

end CFSG.RankThree.GF2n.Stroth80.Tri

end
