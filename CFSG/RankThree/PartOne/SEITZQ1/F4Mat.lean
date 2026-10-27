module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Tactic.LinearCombination

public section

namespace CFSG.RankThree.PartOne.SEITZQ1

open Matrix

@[expose] def f4Add (x y : Fin 4) : Fin 4 :=
  (![![0, 1, 2, 3], ![1, 0, 3, 2], ![2, 3, 0, 1], ![3, 2, 1, 0]] : Fin 4 → Fin 4 → Fin 4) x y

@[expose] def f4Mul (x y : Fin 4) : Fin 4 :=
  (![![0, 0, 0, 0], ![0, 1, 2, 3], ![0, 2, 3, 1], ![0, 3, 1, 2]] : Fin 4 → Fin 4 → Fin 4) x y

variable {R : Type*} [CommRing R]

@[expose] def f4Ev (ω : R) (x : Fin 4) : R := ![0, 1, ω, ω + 1] x

variable [CharP R 2] {ω : R}

theorem f4Ev_add (x y : Fin 4) :
    f4Ev ω (f4Add x y) = f4Ev ω x + f4Ev ω y := by
  have h2 : (2 : R) = 0 := CharTwo.two_eq_zero
  fin_cases x <;> fin_cases y <;> simp [f4Add, f4Ev] <;>
    first
    | ring1
    | linear_combination h2
    | linear_combination (-1 : R) * h2
    | linear_combination ω * h2
    | linear_combination (-ω) * h2
    | linear_combination (ω + 1) * h2
    | linear_combination (-ω - 1) * h2

theorem f4Ev_mul (hω : ω ^ 2 + ω + 1 = 0) (x y : Fin 4) :
    f4Ev ω (f4Mul x y) = f4Ev ω x * f4Ev ω y := by
  have h2 : (2 : R) = 0 := CharTwo.two_eq_zero
  fin_cases x <;> fin_cases y <;> simp [f4Mul, f4Ev] <;>
    first
    | ring1
    | linear_combination hω
    | linear_combination (-1 : R) * hω
    | linear_combination hω - (ω + 1) * h2
    | linear_combination (-1 : R) * hω + (ω + 1) * h2
    | linear_combination hω - h2
    | linear_combination (-1 : R) * hω + h2

abbrev F4M : Type := Fin 3 → Fin 3 → Fin 4

@[expose] def f4MMul (A B : F4M) : F4M := fun i j =>
  f4Add (f4Add (f4Mul (A i 0) (B 0 j)) (f4Mul (A i 1) (B 1 j))) (f4Mul (A i 2) (B 2 j))

@[expose] def f4MOne : F4M := fun i j => if i = j then 1 else 0

@[expose] def f4MTv (i j : Fin 3) (t : Fin 4) : F4M := fun k l =>
  if k = l then 1 else if k = i ∧ l = j then t else 0

@[expose] def f4MStar (A : F4M) : F4M := fun i j => f4Mul (A j i) (A j i)

@[expose] def f4MDet (A : F4M) : Fin 4 :=
  f4Add (f4Add (f4Add (f4Mul (f4Mul (A 0 0) (A 1 1)) (A 2 2)) (f4Mul (f4Mul (A 0 1) (A 1 2)) (A 2 0)))
    (f4Add (f4Mul (f4Mul (A 0 2) (A 1 0)) (A 2 1)) (f4Mul (f4Mul (A 0 2) (A 1 1)) (A 2 0))))
    (f4Add (f4Mul (f4Mul (A 0 1) (A 1 0)) (A 2 2)) (f4Mul (f4Mul (A 0 0) (A 1 2)) (A 2 1)))

@[expose] def f4MEv (ω : R) (A : F4M) : Matrix (Fin 3) (Fin 3) R :=
  Matrix.of fun i j => f4Ev ω (A i j)

theorem f4MEv_mul (hω : ω ^ 2 + ω + 1 = 0) (A B : F4M) :
    f4MEv ω (f4MMul A B) = f4MEv ω A * f4MEv ω B := by
  ext i j
  simp only [f4MEv, f4MMul, Matrix.of_apply, Matrix.mul_apply, Fin.sum_univ_three, f4Ev_add,
    f4Ev_mul hω]

omit [CharP R 2] in
theorem f4MEv_one : f4MEv ω f4MOne = 1 := by
  ext i j
  simp only [f4MEv, f4MOne, Matrix.of_apply, Matrix.one_apply]
  split_ifs <;> rfl

omit [CharP R 2] in
theorem f4MEv_tv {i j : Fin 3} (hij : i ≠ j) (t : Fin 4) :
    f4MEv ω (f4MTv i j t) = 1 + Matrix.single i j (f4Ev ω t) := by
  ext k l
  simp only [f4MEv, f4MTv, Matrix.of_apply, Matrix.add_apply, Matrix.one_apply,
    Matrix.single_apply]
  by_cases hkl : k = l
  · subst hkl
    have : ¬(i = k ∧ j = k) := fun h => hij (h.1.trans h.2.symm)
    simp [this, f4Ev]
  · by_cases h : k = i ∧ l = j
    · obtain ⟨rfl, rfl⟩ := h
      simp [hkl]
    · have h' : ¬(i = k ∧ j = l) := fun h'' => h ⟨h''.1.symm, h''.2.symm⟩
      simp [hkl, h, h', f4Ev]

theorem f4MEv_det (hω : ω ^ 2 + ω + 1 = 0) (A : F4M) :
    (f4MEv ω A).det = f4Ev ω (f4MDet A) := by
  rw [Matrix.det_fin_three]
  simp only [f4MEv, Matrix.of_apply, f4MDet, f4Ev_add, f4Ev_mul hω, CharTwo.sub_eq_add]
  ring

theorem f4Ev_map_sq (Fr : R →+* R) (hFr : Fr ω = ω + 1) (x : Fin 4) :
    Fr (f4Ev ω x) = f4Ev ω (f4Mul x x) := by
  have h2 : (2 : R) = 0 := CharTwo.two_eq_zero
  fin_cases x <;> simp [f4Ev, f4Mul, hFr]
  linear_combination h2

theorem f4MEv_map_transpose (Fr : R →+* R) (hFr : Fr ω = ω + 1)
    (A : F4M) : ((f4MEv ω A).map Fr)ᵀ = f4MEv ω (f4MStar A) := by
  ext i j
  simp only [Matrix.transpose_apply, Matrix.map_apply, f4MEv, Matrix.of_apply, f4MStar,
    f4Ev_map_sq Fr hFr]

@[expose] def q1LetterF4 : Fin 9 → F4M
  | 0 => ![![0, 1, 0], ![0, 0, 1], ![1, 0, 0]]
  | 1 => ![![1, 1, 1], ![1, 2, 3], ![1, 3, 2]]
  | 2 => ![![1, 1, 1], ![1, 3, 2], ![1, 2, 3]]
  | 3 => ![![1, 1, 1], ![2, 1, 3], ![3, 1, 2]]
  | 4 => ![![1, 1, 2], ![1, 3, 3], ![3, 1, 3]]
  | 5 => ![![1, 1, 2], ![3, 2, 2], ![1, 2, 1]]
  | 6 => ![![1, 2, 2], ![1, 3, 1], ![2, 2, 1]]
  | 7 => ![![2, 1, 2], ![1, 2, 2], ![1, 1, 3]]
  | 8 => ![![2, 1, 3], ![3, 1, 2], ![1, 1, 1]]

@[expose] def q1LetterDec : Fin 9 → List (Fin 3 × Fin 3 × Fin 4)
  | 0 => [(0, 2, 1), (2, 0, 1), (1, 2, 1), (0, 1, 1), (2, 1, 1), (0, 2, 1), (1, 2, 1)]
  | 1 => [(1, 0, 1), (2, 0, 1), (1, 2, 1), (0, 1, 1), (2, 1, 2), (1, 2, 1)]
  | 2 => [(1, 0, 1), (2, 0, 1), (1, 2, 1), (0, 1, 1), (2, 1, 3), (1, 2, 1)]
  | 3 => [(1, 0, 2), (2, 0, 3), (1, 2, 1), (0, 1, 1), (2, 1, 2), (0, 2, 1)]
  | 4 => [(1, 0, 1), (2, 0, 3), (1, 2, 2), (0, 1, 1), (2, 1, 2), (1, 2, 2)]
  | 5 => [(1, 0, 3), (2, 0, 1), (0, 1, 1), (2, 1, 3), (0, 2, 1), (1, 2, 3)]
  | 6 => [(1, 0, 1), (2, 0, 2), (0, 1, 2), (2, 1, 1), (0, 2, 3), (1, 2, 3)]
  | 7 => [(0, 1, 3), (1, 0, 1), (2, 0, 1), (1, 2, 3), (2, 1, 1), (0, 2, 3), (1, 2, 1)]
  | 8 => [(0, 1, 1), (1, 0, 3), (2, 0, 1), (2, 1, 1), (0, 2, 1), (1, 2, 1)]

@[expose] def f4MProd (l : List (Fin 3 × Fin 3 × Fin 4)) : F4M :=
  l.foldr (fun x A => f4MMul (f4MTv x.1 x.2.1 x.2.2) A) f4MOne

theorem q1Letter_checks : ∀ k : Fin 9, f4MDet (q1LetterF4 k) = 1 ∧
    f4MMul (f4MStar (q1LetterF4 k)) (q1LetterF4 k) = f4MOne ∧
    f4MProd (q1LetterDec k) = q1LetterF4 k ∧ ∀ x ∈ q1LetterDec k, x.1 ≠ x.2.1 := by
  decide

end CFSG.RankThree.PartOne.SEITZQ1
